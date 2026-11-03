import Langlands.GroupScheme.Torus.WeilRestrictionNormOneFixedStatements

/-! # Fixed-vector vanishing for the actual norm-one Galois lattices -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.Algebra.SeparableTensor

namespace Langlands.GroupScheme.WeilGm

variable (k K Ω : Type u) [Field k] [Field K] [Field Ω]
  [Algebra k K] [Algebra k Ω]

/-- Normality extends the isomorphism between any two embedded copies of `K`. -/
theorem embeddingActionTransitive [Normal k Ω] :
    embeddingActionTransitiveStatement k K Ω := by
  intro τ υ
  let e : τ.fieldRange ≃ₐ[k] υ.fieldRange :=
    τ.equivFieldRange.symm.trans υ.equivFieldRange
  refine ⟨e.liftNormal Ω, ?_⟩
  ext x
  change e.liftNormal Ω (τ x) = υ x
  simpa [e] using e.liftNormal_commutes Ω (τ.equivFieldRange x)

private theorem embedding_fixed_coordinates_eq
    (htrans : embeddingActionTransitiveStatement k K Ω)
    (m : (K →ₐ[k] Ω) → ℤ)
    (hm : ∀ σ : Ω ≃ₐ[k] Ω, embeddingPermutationRepresentation k K Ω σ m = m)
    (τ υ : K →ₐ[k] Ω) : m τ = m υ := by
  obtain ⟨σ, hσ⟩ := htrans τ υ
  have he := congrFun (hm σ) υ
  change m ((embeddingPermutation k K Ω σ).symm υ) = m υ at he
  have hi : (embeddingPermutation k K Ω σ).symm υ = τ := by
    rw [← hσ, Equiv.symm_apply_apply]
  rwa [hi] at he

variable [FiniteDimensional k K]

private theorem embedding_constant_eq_zero [Nonempty (K →ₐ[k] Ω)]
    (c : ℤ) (hc : embeddingCoordinateSum k K Ω (fun _ => c) = 0) : c = 0 := by
  have hcard : (Fintype.card (K →ₐ[k] Ω) : ℤ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hmul : (Fintype.card (K →ₐ[k] Ω) : ℤ) * c = 0 := by
    simpa [embeddingCoordinateSum, nsmul_eq_mul] using hc
  exact (mul_eq_zero.mp hmul).resolve_left hcard

/-- A transitive action on a nonempty embedding set has no fixed sum-zero vector. -/
theorem embeddingSumZeroFixed [Nonempty (K →ₐ[k] Ω)]
    (htrans : embeddingActionTransitiveStatement k K Ω) :
    embeddingSumZeroFixedStatement k K Ω := by
  intro m
  constructor
  · intro hm
    obtain ⟨τ₀⟩ := ‹Nonempty (K →ₐ[k] Ω)›
    have hm' : ∀ σ : Ω ≃ₐ[k] Ω,
        embeddingPermutationRepresentation k K Ω σ m.val = m.val :=
      fun σ => congrArg Subtype.val (hm σ)
    have hconst : m.val = fun _ => m.val τ₀ :=
      funext fun τ => embedding_fixed_coordinates_eq k K Ω htrans m.val hm' τ τ₀
    have hc : m.val τ₀ = 0 := embedding_constant_eq_zero k K Ω _ (by
      rw [← hconst]
      exact m.property)
    apply Subtype.ext
    change m.val = 0
    rw [hconst, hc]
    rfl
  · rintro rfl
    intro σ
    exact map_zero _

/-- Class invariance forces representative invariance, because the constant
difference has zero coordinate sum. Transitivity then makes the class zero. -/
theorem embeddingQuotientFixed [Nonempty (K →ₐ[k] Ω)]
    (htrans : embeddingActionTransitiveStatement k K Ω) :
    embeddingQuotientFixedStatement k K Ω := by
  intro m
  constructor
  · refine Submodule.Quotient.induction_on (embeddingDiagonal k K Ω) m ?_
    intro f hf
    have hfixed : ∀ σ : Ω ≃ₐ[k] Ω,
        embeddingPermutationRepresentation k K Ω σ f = f := by
      intro σ
      have hdiff :
          embeddingPermutationRepresentation k K Ω σ f - f ∈ embeddingDiagonal k K Ω :=
        (Submodule.Quotient.eq _).mp (by
          rw [← embeddingQuotientRepresentation_mk]
          exact hf σ)
      obtain ⟨c, hc⟩ := (mem_embeddingDiagonal_iff k K Ω _).mp hdiff
      have hsum : embeddingCoordinateSum k K Ω (fun _ => c) = 0 := by
        rw [← hc, map_sub, embeddingCoordinateSum_permutation, sub_self]
      have hc0 := embedding_constant_eq_zero k K Ω c hsum
      apply sub_eq_zero.mp
      rw [hc, hc0]
      rfl
    obtain ⟨τ₀⟩ := ‹Nonempty (K →ₐ[k] Ω)›
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    apply (mem_embeddingDiagonal_iff k K Ω f).mpr
    exact ⟨f τ₀, funext fun τ =>
      embedding_fixed_coordinates_eq k K Ω htrans f hfixed τ τ₀⟩
  · rintro rfl
    intro σ
    exact map_zero _

variable [Algebra.IsSeparable k K]
  (hsplit : ∀ x : K, ((minpoly k x).map (algebraMap k Ω)).Splits)

include hsplit in
/-- The published ordinary equivariance transfers the sum-zero fixed-vector result. -/
theorem normOneCocharacterFixed
    (hfixed : embeddingSumZeroFixedStatement k K Ω) :
    normOneCocharacterFixedStatement k K Ω := by
  intro ν
  let e := normOneSeparableEmbeddingCocharacterEquiv k K Ω hsplit
  constructor
  · intro hν
    have he : e ν = 0 := (hfixed (e ν)).mp (fun σ => by
      rw [← normOneSeparableEmbeddingCocharacterEquiv_equivariant k K Ω hsplit]
      exact congrArg e (hν σ))
    exact e.injective (he.trans e.map_zero.symm)
  · rintro rfl
    intro σ
    exact map_zero _

include hsplit in
/-- The published ordinary equivariance transfers the quotient fixed-class result. -/
theorem normOneCharacterFixed
    (hfixed : embeddingQuotientFixedStatement k K Ω) :
    normOneCharacterFixedStatement k K Ω := by
  intro χ
  let e := normOneSeparableEmbeddingCharacterEquiv k K Ω hsplit
  constructor
  · intro hχ
    have he : e χ = 0 := (hfixed (e χ)).mp (fun σ => by
      rw [← normOneSeparableEmbeddingCharacterEquiv_equivariant k K Ω hsplit]
      exact congrArg e (hχ σ))
    exact e.injective (he.trans e.map_zero.symm)
  · rintro rfl
    intro σ
    exact map_zero _

omit [Algebra.IsSeparable k K] in
/-- Embedding transitivity and fixed-vector vanishing for both coordinate lattices
and both actual norm-one Galois lattices, with the exact published premises. -/
theorem normOneGaloisFixedLattices : normOneGaloisFixedLatticesStatement k K Ω := by
  intro hsep hnormal hsplit
  let := hsep
  let := hnormal
  let := separableEmbedding_nonempty k K Ω hsplit
  have htrans := embeddingActionTransitive k K Ω
  have hsum := embeddingSumZeroFixed k K Ω htrans
  have hquot := embeddingQuotientFixed k K Ω htrans
  exact ⟨htrans, hsum, hquot,
    normOneCocharacterFixed k K Ω hsplit hsum,
    normOneCharacterFixed k K Ω hsplit hquot⟩

end Langlands.GroupScheme.WeilGm
