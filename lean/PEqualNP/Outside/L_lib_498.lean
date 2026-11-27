import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_498 :
    ∀ (n p q : ℕ) (A : Fin p → Finset (Fin n × Bool))
      (B : Fin q → Finset (Fin n × Bool)) (x : Fin n → Bool),
      let holds := fun C : Finset (Fin n × Bool) => ∃ l ∈ C, x l.1 = l.2
      (∃ t : Bool, (∀ i, holds (A i) ∨ t = true) ∧ (∀ j, holds (B j) ∨ t = false)) ↔
        ∀ i j, holds (A i ∪ B j) := by
  intro n p q A B x
  let holds (C : Finset (Fin n × Bool)) : Prop := ∃ l ∈ C, x l.1 = l.2
  change (∃ t : Bool, (∀ i, holds (A i) ∨ t = true) ∧
    (∀ j, holds (B j) ∨ t = false)) ↔ ∀ i j, holds (A i ∪ B j)
  have union_holds (S T : Finset (Fin n × Bool)) :
      holds (S ∪ T) ↔ holds S ∨ holds T := by
    simp only [holds, Finset.mem_union, or_and_right, exists_or]
  simp_rw [union_holds]
  constructor
  · rintro ⟨t, hA, hB⟩ i j
    cases t
    · exact Or.inl ((hA i).resolve_right (by decide))
    · exact Or.inr ((hB j).resolve_right (by decide))
  · intro resolved
    by_cases allA : ∀ i, holds (A i)
    · exact ⟨false, fun i => Or.inl (allA i), fun _ => Or.inr rfl⟩
    · obtain ⟨i, hi⟩ := not_forall.mp allA
      exact ⟨true, fun _ => Or.inr rfl, fun j => Or.inl ((resolved i j).resolve_left hi)⟩
