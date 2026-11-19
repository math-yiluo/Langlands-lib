import Langlands.Representation.Plancherel.ContinuedIntertwiningScalarNaturality

/-! # Composite rational scalars under surjective restriction -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Plancherel

open UnramifiedOperatorFamily

section OpenSquare

variable {H : Type*} [Group H] [TopologicalSpace H]
  {I : Type*} {ν : I → (H →* ℝ≥0ˣ)}
  {V W V' W' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
  {Ω Ω' : Set (unramifiedCharacters ν)}

/-- Fixed linear maps intertwine the original operators on a nonempty
ambient open subset of both regions. -/
def HasOpenLinearSquare (A : Ω → V →ₗ[ℂ] W) (A' : Ω' → V' →ₗ[ℂ] W')
    (S : V →ₗ[ℂ] V') (T : W →ₗ[ℂ] W') : Prop :=
  ∃ (D : Set (unramifiedCharacters ν)) (_ : IsOpen D) (_ : D.Nonempty)
    (hD : D ⊆ Ω) (hD' : D ⊆ Ω'),
    ∀ z (hz : z ∈ D), (A' ⟨z, hD' hz⟩).comp S = T.comp (A ⟨z, hD hz⟩)

end OpenSquare

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints L)]
  (hp : Continuous (rationalValuationImageProjection L))
  (hL : GroupScheme.IsConnectedReductive L)
  {V W V' W' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']

set_option hygiene false in
local notation "Z" => unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul)

variable {Ω Λ Ω' Λ' : Set Z}
  {A : Ω → V →ₗ[ℂ] W} {B : Λ → W →ₗ[ℂ] V}
  {A' : Ω' → V' →ₗ[ℂ] W'} {B' : Λ' → W' →ₗ[ℂ] V'}
  (p : RationalOperatorContinuationData Ω A) (q : RationalOperatorContinuationData Λ B)
  (p' : RationalOperatorContinuationData Ω' A') (q' : RationalOperatorContinuationData Λ' B')
  (S : V →ₗ[ℂ] V') (T : W →ₗ[ℂ] W')

include hp hL in
/-- The two restriction squares descend the composite on the common
regular region. The original forward and reverse open sets are independent. -/
theorem continuedComposite_linear_square
    (hA : HasOpenLinearSquare A A' S T) (hB : HasOpenLinearSquare B B' T S)
    (z : ↥((p.regularRegion ∩ q.regularRegion) ∩ (p'.regularRegion ∩ q'.regularRegion))) :
    (p'.continuedComposite q' ⟨z.val, z.property.2⟩).comp S =
      S.comp (p.continuedComposite q ⟨z.val, z.property.1⟩) := by
  obtain ⟨D, hD, hnD, hDΩ, hDΩ', hDnat⟩ := hA
  obtain ⟨E, hE, hnE, hEΛ, hEΛ', hEnat⟩ := hB
  have hF := rationalOperatorContinuationData_natural L hp hL p p' S T
    hD hnD hDΩ hDΩ' hDnat ⟨z.val, z.property.1.1, z.property.2.1⟩
  have hR := rationalOperatorContinuationData_natural L hp hL q q' T S
    hE hnE hEΛ hEΛ' hEnat ⟨z.val, z.property.1.2, z.property.2.2⟩
  change (q'.continuedOperator ⟨z.val, z.property.2.2⟩).comp
      ((p'.continuedOperator ⟨z.val, z.property.2.1⟩).comp S) =
    (S.comp (q.continuedOperator ⟨z.val, z.property.1.2⟩)).comp
      (p.continuedOperator ⟨z.val, z.property.1.1⟩)
  rw [hF, ← LinearMap.comp_assoc, hR]

/-- Surjectivity of the restriction on the starting model transfers generic
scalarity and identifies the extracted rational scalars exactly. -/
theorem continuedCompositeRationalScalar_eq_of_surjective_restriction
    (hA : HasOpenLinearSquare A A' S T) (hB : HasOpenLinearSquare B B' T S)
    (hS : Function.Surjective S)
    (hΩ : Ω.Nonempty) (hΛ : Λ.Nonempty) (hΩ' : Ω'.Nonempty) (hΛ' : Λ'.Nonempty)
    {U : Set Z} (hU : IsOpen U) (hneU : U.Nonempty)
    (hscalar : ∀ z : ↥(p.regularRegion ∩ q.regularRegion), z.val ∈ U →
      ∃ a : ℂ, p.continuedComposite q z = a • LinearMap.id)
    (v : V) (ℓ : V →ₗ[ℂ] ℂ) (hℓ : ℓ v = 1)
    (w : V') (m : V' →ₗ[ℂ] ℂ) (hm : m w = 1) :
    continuedCompositeRationalScalar L hp hL p q hΩ hΛ v ℓ =
      continuedCompositeRationalScalar L hp hL p' q' hΩ' hΛ' w m := by
  have hR := p.regularRegion_isOpen.inter q.regularRegion_isOpen
  have hR' := p'.regularRegion_isOpen.inter q'.regularRegion_isOpen
  have hdR := continuedCompositeRegion_dense L hp hL p q hΩ hΛ
  have hdR' := continuedCompositeRegion_dense L hp hL p' q' hΩ' hΛ'
  have hnUR := hdR.inter_open_nonempty U hU hneU
  have hsca := rationalUnramifiedScalarContinuation L hp hL
    (hU.inter hR) hnUR Set.inter_subset_right
    (p.continuedComposite q) (p.continuedComposite_rational q) v ℓ hℓ
    (fun z hz => hscalar ⟨z, hz.2⟩ hz.1)
  apply ScalarPresentation.toFunctionField_eq_of_eqOn_isOpen L hp hL
    _ _ hdR.nonempty hdR'.nonempty (hR.inter hR')
    (hdR'.inter_open_nonempty _ hR hdR.nonempty) Set.inter_subset_left Set.inter_subset_right
  intro z hz
  have hre := continuedComposite_linear_square L hp hL p q p' q' S T hA hB ⟨z, hz⟩
  have hsca' : p'.continuedComposite q' ⟨z, hz.2⟩ =
      endomorphismScalarCoefficient v ℓ (p.continuedComposite q ⟨z, hz.1⟩) • LinearMap.id := by
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := hS y
    have hh := LinearMap.congr_fun hre x
    change p'.continuedComposite q' ⟨z, hz.2⟩ (S x) =
      S (p.continuedComposite q ⟨z, hz.1⟩ x) at hh
    have hx := LinearMap.congr_fun (hsca ⟨z, hz.1⟩) x
    exact hh.trans (by
      simpa only [LinearMap.smul_apply, LinearMap.id_apply, map_smul] using congrArg S hx)
  rw [hsca', endomorphismScalarCoefficient_smul_id w m hm]

end Langlands.Plancherel
