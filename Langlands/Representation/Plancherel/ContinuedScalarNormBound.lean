import Langlands.Representation.Plancherel.DynamicOppositeUnitaryNonnegativity
import Langlands.Representation.Plancherel.InverseQuadraticCoefficientBound

/-! # A uniform bound for the inverse of an adjoint composite scalar -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

open UnramifiedOperatorFamily

universe u uV uW

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints L)]
  (hp : Continuous (rationalValuationImageProjection L))
  (hL : GroupScheme.IsConnectedReductive L)

set_option hygiene false in
local notation "RL" =>
  unramifiedRegularFunctions (fun ψ => (rationalNormCharacters L ψ).toMul)

set_option hygiene false in
local notation "XL" =>
  unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul)

set_option hygiene false in
local notation "KL" => rationalUnramifiedFunctionField L hp hL

/-- A rational function is regular at a parameter and its value has norm at
most `C`, as witnessed by a fraction with nonzero denominator there. -/
def RationalFunctionNormBoundedAt (f : KL) (z : XL) (C : ℝ) : Prop :=
  ∃ m n : RL, n.val z ≠ 0 ∧
    f = algebraMap RL KL m / algebraMap RL KL n ∧
    ‖m.val z / n.val z‖ ≤ C

variable {L hp hL}

/-- The denominator in a bounded value witnesses regularity. -/
theorem RationalFunctionNormBoundedAt.regularAt {f : KL} {z : XL} {C : ℝ}
    (h : RationalFunctionNormBoundedAt L hp hL f z C) :
    RationalFunctionRegularAt L hp hL f z := by
  obtain ⟨m, n, hn, hf, -⟩ := h
  exact ⟨m, n, hn, hf⟩

variable (L hp hL)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {Ω Λ : Set XL} {A : Ω → V →ₗ[ℂ] W} {B : Λ → W →ₗ[ℂ] V}

/-- A fixed nonzero detecting functional gives a uniform inverse-scalar
bound at all self-dual common regular parameters. The source form need only
have a nonzero diagonal on the extracting vector; the target form is positive
definite. No parameter compactness is used. -/
theorem exists_continuedCompositeRationalScalar_inv_norm_bound
    (sV : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (sW : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ)
    (cW : InnerProductSpace.Core ℂ W)
    (hcore : ∀ w w' : W, sW w w' = cW.inner w w')
    (p : RationalOperatorContinuationData Ω A) (q : RationalOperatorContinuationData Λ B)
    {D : Set XL} (hD : IsOpen D) (hne : D.Nonempty) (hDΩ : D ⊆ Ω)
    (hdag : ∀ w ∈ D, unramifiedConjInv _ w ∈ Λ)
    (hadj : ∀ w (hw : w ∈ D) (v : V) (w' : W),
      sW (A ⟨w, hDΩ hw⟩ v) w' = sV v (B ⟨unramifiedConjInv _ w, hdag w hw⟩ w'))
    (hΩ : Ω.Nonempty) (hΛ : Λ.Nonempty) (v : V) (hv : sV v v ≠ 0)
    (f : KL)
    (hf : f = continuedCompositeRationalScalar L hp hL p q hΩ hΛ v
      ((sV v v)⁻¹ • sV v))
    (ℓ : W →ₗ[ℂ] ℂ) (a : ℂ) (ha : a ≠ 0)
    (hconst : ∀ z : p.regularRegion, ℓ (p.continuedOperator z v) = a) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : XL,
      z ∈ p.regularRegion ∩ q.regularRegion → unramifiedConjInv _ z = z →
      RationalFunctionNormBoundedAt L hp hL f⁻¹ z C := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_inverseQuadraticCoefficient_norm_bound p v cW ℓ a ha hconst
  refine ⟨‖sV v v‖ * C, mul_pos (norm_pos_iff.mpr hv) hC, ?_⟩
  intro z hz hzdag
  obtain ⟨m, n, -, hnreg, hfrac, hval⟩ :=
    continuedCompositeRationalScalar_spec L hp hL p q hΩ hΛ v ((sV v v)⁻¹ • sV v)
  have hz' : unramifiedConjInv _ (⟨z, hz.1⟩ : p.regularRegion).val ∈ q.regularRegion := by
    change unramifiedConjInv _ z ∈ q.regularRegion
    rw [hzdag]
    exact hz.2
  have hadjz := continuedOperator_adjoint L hp hL sV sW p q hD hne hDΩ hdag hadj
    ⟨z, hz.1⟩ hz' v (p.continuedOperator ⟨z, hz.1⟩ v)
  have hcongr : q.continuedOperator ⟨unramifiedConjInv _ z, hz'⟩ =
      q.continuedOperator ⟨z, hz.2⟩ := continuedOperator_congr L q hz' hz.2 hzdag
  rw [hcongr] at hadjz
  have he : m.val z / n.val z =
      (sV v v)⁻¹ * cW.inner (p.continuedOperator ⟨z, hz.1⟩ v)
        (p.continuedOperator ⟨z, hz.1⟩ v) := by
    rw [← hval ⟨z, hz⟩]
    change (sV v v)⁻¹ * sV v (q.continuedOperator ⟨z, hz.2⟩
      (p.continuedOperator ⟨z, hz.1⟩ v)) = _
    rw [← hadjz, hcore]
  have hw : p.continuedOperator ⟨z, hz.1⟩ v ≠ 0 := by
    intro hw
    apply ha
    rw [← hconst ⟨z, hz.1⟩, hw, map_zero]
  have hdiag : cW.inner (p.continuedOperator ⟨z, hz.1⟩ v)
      (p.continuedOperator ⟨z, hz.1⟩ v) ≠ 0 :=
    fun h0 => hw (cW.definite _ h0)
  have hm : m.val z ≠ 0 := by
    intro hm
    have h0 := he
    rw [hm, zero_div] at h0
    exact (mul_ne_zero (inv_ne_zero hv) hdiag) h0.symm
  refine ⟨n, m, hm, by rw [hf, hfrac, inv_div], ?_⟩
  rw [← inv_div, he, mul_inv_rev, inv_inv, norm_mul]
  calc
    ‖(cW.inner (p.continuedOperator ⟨z, hz.1⟩ v)
        (p.continuedOperator ⟨z, hz.1⟩ v))⁻¹‖ * ‖sV v v‖
        ≤ C * ‖sV v v‖ :=
      mul_le_mul_of_nonneg_right (hbound ⟨z, hz.1⟩) (norm_nonneg _)
    _ = ‖sV v v‖ * C := mul_comm _ _

end Langlands.Plancherel
