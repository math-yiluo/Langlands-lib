import Langlands.Representation.Filtration.LengthTwoUniqueSubrepresentationStatement
import Langlands.Representation.Filtration.MultiplicityAdditivityProof

/-! The actual unique-subrepresentation conclusion of the length-two count argument. -/

namespace Langlands

universe uK uG uV uW

namespace LengthTwo

variable {k : Type uK} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]
  {A : SmoothRep.{uK, uG, uV} k G}
  {W : Type uW} [AddCommGroup W] [Module k W] {σ : Representation k G W}
  {μ : Subrepresentation A.representation → ℕ}

/-- Every nonzero proper invariant subspace has count one. -/
theorem count_eq_one_of_proper (hμ : StrictMono μ) (hμ0 : μ ⊥ = 0)
    (hμ2 : μ ⊤ ≤ 2) {S : Subrepresentation A.representation}
    (hS0 : S ≠ ⊥) (hS1 : S ≠ ⊤) : μ S = 1 := by
  have := count_pos hμ hμ0 hS0
  have := hμ (lt_top_iff_ne_top.mpr hS1)
  omega

/-- A reducible representation admitting a nonzero map has a nonzero proper
invariant subspace. The map rules out the zero representation. -/
theorem exists_proper_of_not_irreducible
    (f : A.representation.IntertwiningMap σ) (hf : f ≠ 0)
    (hred : ¬ A.IsIrreducible) :
    ∃ S : Subrepresentation A.representation, S ≠ ⊥ ∧ S ≠ ⊤ := by
  classical
  have hbt := bot_ne_top_of_ne_zero f hf
  let : Nontrivial (Subrepresentation A.representation) := ⟨⟨⊥, ⊤, hbt⟩⟩
  by_contra h
  apply hred
  refine ⟨fun S => ?_⟩
  by_cases hS : S = ⊥
  · exact Or.inl hS
  · exact Or.inr (by by_contra hS'; exact h ⟨S, hS, hS'⟩)

/-- The actual smooth subrepresentation and quotient are the two simple
factors of the count-bounded two-step filtration. -/
theorem proper_subrepresentation_and_quotient_irreducible
    (hμ : StrictMono μ) (hμ0 : μ ⊥ = 0) (hμ2 : μ ⊤ ≤ 2)
    {S : Subrepresentation A.representation} (hS0 : S ≠ ⊥) (hS1 : S ≠ ⊤) :
    (SmoothRep.subrepresentation A S).IsIrreducible ∧
      (SmoothRep.quotient A S).IsIrreducible := by
  have hS := count_eq_one_of_proper hμ hμ0 hμ2 hS0 hS1
  have hs : (twoStep S).HasSimpleFactors :=
    twoStep_hasSimpleFactors
      (covBy_of_count hμ (bot_lt_iff_ne_bot.mpr hS0) (by omega))
      (covBy_of_count hμ (lt_top_iff_ne_top.mpr hS1) (by omega))
  let i := SmoothRep.hom (SmoothRep.subtype A S)
  let q := SmoothRep.hom (SmoothRep.mkQ A S)
  have hi : Function.Injective i := SmoothRep.subtype_injective A S
  have hq : Function.Surjective q := SmoothRep.mkQ_surjective A S
  have hex : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap := by
    change LinearMap.range S.toSubmodule.subtype = LinearMap.ker S.toSubmodule.mkQ
    rw [Submodule.range_subtype, Submodule.ker_mkQ]
  have hr : i.range = S := by
    apply Subrepresentation.toSubmodule_injective
    exact Submodule.range_subtype _
  obtain ⟨⟨e₀⟩, ⟨e₁⟩⟩ := MultiplicityAdditivityProof.two_step_equivs i q hi hq hex
  rw [hr] at e₀ e₁
  exact ⟨isIrreducible_of_equiv e₀ (hs 0), isIrreducible_of_equiv e₁ (hs 1)⟩

/-- Every nonzero proper invariant subspace is the actual kernel of the given
nonzero intertwiner, provided every count-one subspace is killed. -/
theorem eq_ker_of_count_le_two (hμ : StrictMono μ) (hμ0 : μ ⊥ = 0)
    (hμ2 : μ ⊤ ≤ 2) (f : A.representation.IntertwiningMap σ) (hf : f ≠ 0)
    (hkill : ∀ S : Subrepresentation A.representation, μ S = 1 → S ≤ f.ker)
    {S : Subrepresentation A.representation} (hS0 : S ≠ ⊥) (hS1 : S ≠ ⊤) :
    S = f.ker := by
  have hS := count_eq_one_of_proper hμ hμ0 hμ2 hS0 hS1
  have hle := hkill S hS
  have hk0 : f.ker ≠ ⊥ := by
    intro h
    exact hS0 (bot_unique (h ▸ hle))
  have hk1 := ker_ne_top_of_ne_zero f hf
  have hk := count_eq_one_of_proper hμ hμ0 hμ2 hk0 hk1
  rcases hle.lt_or_eq with h | h
  · have := hμ h
    omega
  · exact h

end LengthTwo

/-- The closed algebraic unique-subrepresentation criterion. -/
theorem lengthTwoUniqueSubrepresentationCriterion :
    LengthTwoUniqueSubrepresentationCriterion.{uK, uG, uV, uW} := by
  intro k _ G _ _ A W _ _ σ μ hμ hμ0 hμ2 f hf hred hkill
  obtain ⟨S, hS0, hS1⟩ := LengthTwo.exists_proper_of_not_irreducible f hf hred
  have hS := LengthTwo.count_eq_one_of_proper hμ hμ0 hμ2 hS0 hS1
  have hs : (LengthTwo.twoStep S).HasSimpleFactors :=
    LengthTwo.twoStep_hasSimpleFactors
      (LengthTwo.covBy_of_count hμ (bot_lt_iff_ne_bot.mpr hS0) (by omega))
      (LengthTwo.covBy_of_count hμ (lt_top_iff_ne_top.mpr hS1) (by omega))
  refine ⟨⟨LengthTwo.twoStep S, hs⟩, ⟨S, ⟨hS0, hS1⟩, ?_⟩, ?_⟩
  · intro T hT
    exact (LengthTwo.eq_ker_of_count_le_two hμ hμ0 hμ2 f hf hkill hT.1 hT.2).trans
      (LengthTwo.eq_ker_of_count_le_two hμ hμ0 hμ2 f hf hkill hS0 hS1).symm
  · intro T hT0 hT1
    exact LengthTwo.proper_subrepresentation_and_quotient_irreducible hμ hμ0 hμ2 hT0 hT1

end Langlands
