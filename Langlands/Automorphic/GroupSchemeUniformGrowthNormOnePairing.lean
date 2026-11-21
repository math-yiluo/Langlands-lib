import Langlands.Automorphic.GroupSchemeInvariantForms
import Langlands.Automorphic.GroupSchemeUniformGrowthFrechet
import Langlands.Global.AdelicGroupHaarMeasure
import Langlands.Global.AdelicGroupNormOneFunctorial

/-! # Norm-one pairings in the uniform moderate growth topology -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Filter MeasureTheory
open scoped CategoryTheory.MonObj ENNReal Topology

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions.UniformGrowthFrechetSpace

open Langlands.Global Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G M : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] [IsAffine M.X.left]
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (hN : 0 < N) (hrho : IsClosedSubgroup rho) (R : ℝ)
  (L : Subgroup (FiniteAdelicGroupPoints F G))

local notation "V" => UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L
local notation "valAt" => toFun F G rho hsmooth hcalc hN hrho R L
local notation "Γ" => rationalNormOneSubgroup F M

variable (j : M ⟶ G) (ψ : AdelicGroupPoints F M → ℂ)
  (hψ : IsLeftInvariantUnder F M (rationalSubgroup F M) ψ) (g : AdelicGroupPoints F G)

/-- Pull back a right translate along the group morphism, multiply by the conjugate
test function, and descend to the actual rational norm-one quotient. -/
def normOnePairingIntegrand (f : V) : NormOneRationalQuotient F M → ℂ :=
  LeftCosetSpace.lift Γ
    (fun m => valAt f (AdelicGroupPoints.map F M G j m.val * g) * starRingEnd ℂ (ψ m.val)) (by
      rintro ⟨_, q, rfl⟩ m
      have hq : AdelicGroupPoints.map F M G j (rational F M q) =
          rational F G (M.affinePointsTarget j (CommAlgCat.of F F) q) :=
        (DFunLike.congr_fun (rational_naturality F M j) q).symm
      change valAt f (AdelicGroupPoints.map F M G j (rational F M q * m.val) * g) *
          starRingEnd ℂ (ψ (rational F M q * m.val)) = _
      rw [map_mul, mul_assoc, hq, hψ _ ⟨q, rfl⟩ m.val]
      rw [show valAt f
          (rational F G (M.affinePointsTarget j (CommAlgCat.of F F) q) *
            (AdelicGroupPoints.map F M G j m.val * g)) = valAt f (AdelicGroupPoints.map F M G j m.val * g) from
        (f : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).val.val.val.property _ _])

omit [IsAffine M.X.left] in
@[simp]
theorem normOnePairingIntegrand_mk (f : V) (m : normOneSubgroup F M) :
    normOnePairingIntegrand F G M rho hsmooth hcalc hN hrho R L j ψ hψ g f
      (LeftCosetSpace.mk Γ m) =
        valAt f (AdelicGroupPoints.map F M G j m.val * g) * starRingEnd ℂ (ψ m.val) := rfl

variable [LocallyOfFiniteType M.X.hom]
  (hcont : Continuous ψ)
  (bound : NormOneRationalQuotient F M → ℝ)
  (hbound : Integrable bound (normOneRationalQuotientHaarMeasure F M))
  (hrep : ∀ᵐ (q : NormOneRationalQuotient F M) ∂normOneRationalQuotientHaarMeasure F M,
    ∃ m : normOneSubgroup F M,
      LeftCosetSpace.mk (rationalNormOneSubgroup F M) m = q ∧
      (RepresentationGrowth.adelicSourceNorm F G rho (AdelicGroupPoints.map F M G j m.val * g)) ^ R *
        ‖ψ m.val‖ ≤ bound q)

/-- Under an integrable bound on absolute values of the weighted test function
at quotient representatives, the norm-one pairing is continuous linear in the
ambient function of uniform moderate growth. -/
def normOnePairingEvaluation : V →L[ℂ] ℂ := by
  let measure := normOneRationalQuotientHaarMeasure F M
  let integrand := normOnePairingIntegrand F G M rho hsmooth hcalc hN hrho R L j ψ hψ g
  let weighted := weightedDerivative F G rho hsmooth hcalc hN hrho R L
    (1 : AdelicEnvelopingAlgebra F G hsmooth)
  let weight (x : AdelicGroupPoints F G) := RepresentationGrowth.adelicSourceNorm F G rho x ^ R
  have hw (x : AdelicGroupPoints F G) : 0 < weight x :=
    Real.rpow_pos_of_pos (RepresentationGrowth.adelicSourceNorm_pos F G rho hN x) R
  have hdValue (f : V) (x : AdelicGroupPoints F G) :
      weighted f x = valAt f x * ((weight x : ℝ) : ℂ)⁻¹ := by
    change evaluate F G (adelicEnvelopingAction F G hsmooth hcalc 1
        (f : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).val).val x *
        ((weight x : ℝ) : ℂ)⁻¹ = _
    rw [map_one, Module.End.one_apply]
    rfl
  have hdSub (f h : V) : weighted (f - h) = weighted f - weighted h := by
    apply Subtype.ext
    funext x
    change weighted (f - h) x = weighted f x - weighted h x
    rw [hdValue, hdValue, hdValue]
    rw [sub_eq_add_neg f h, ← neg_one_smul ℂ h]
    change (valAt f x + (-1 : ℂ) * valAt h x) * _ = _
    ring
  have hdBound (f : V) (x : AdelicGroupPoints F G) :
      ‖valAt f x‖ ≤ ‖weighted f‖ * weight x := by
    have hz := lp.norm_apply_le_norm ENNReal.top_ne_zero (weighted f) x
    rw [hdValue, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hw x),
      ← div_eq_mul_inv] at hz
    exact (div_le_iff₀ (hw x)).mp hz
  have hcontIntegrand (f : V) : Continuous (integrand f) := by
    apply (LeftCosetSpace.continuous_iff Γ).mpr
    change Continuous (fun m : normOneSubgroup F M =>
      valAt f (AdelicGroupPoints.map F M G j m.val * g) * starRingEnd ℂ (ψ m.val))
    have hf : Continuous (valAt f) :=
      (f : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).val.val.property
    exact (hf.comp (((AdelicGroupPoints.map F M G j).continuous.comp continuous_subtype_val).mul
      continuous_const)).mul (Complex.continuous_conj.comp (hcont.comp continuous_subtype_val))
  have hdom (f : V) : ∀ᵐ q ∂measure, ‖integrand f q‖ ≤ ‖weighted f‖ * bound q := by
    filter_upwards [hrep] with q hq
    obtain ⟨m, hm, hmq⟩ := hq
    rw [← hm]
    change ‖valAt f (AdelicGroupPoints.map F M G j m.val * g) * starRingEnd ℂ (ψ m.val)‖ ≤ _
    rw [norm_mul, Complex.norm_conj, hm]
    calc
      _ ≤ (‖weighted f‖ * weight (AdelicGroupPoints.map F M G j m.val * g)) * ‖ψ m.val‖ :=
        mul_le_mul_of_nonneg_right (hdBound f _) (norm_nonneg _)
      _ ≤ ‖weighted f‖ * bound q := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hmq (norm_nonneg _)
  have hIntegrable (f : V) : Integrable (integrand f) measure :=
    (hbound.const_mul ‖weighted f‖).mono' (hcontIntegrand f).aestronglyMeasurable (hdom f)
  let operator : V →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ q, integrand f q ∂measure
      map_add' := by
        intro f h
        have hAdd : integrand (f + h) = integrand f + integrand h := by
          funext q
          obtain ⟨m, rfl⟩ := LeftCosetSpace.mk_surjective Γ q
          change (valAt f _ + valAt h _) * _ = valAt f _ * _ + valAt h _ * _
          exact add_mul _ _ _
        change ∫ q, integrand (f + h) q ∂measure = _
        rw [hAdd]
        exact integral_add (hIntegrable f) (hIntegrable h)
      map_smul' := by
        intro z f
        have hSmul : integrand (z • f) = z • integrand f := by
          funext q
          obtain ⟨m, rfl⟩ := LeftCosetSpace.mk_surjective Γ q
          change (z * valAt f _) * _ = z * (valAt f _ * _)
          exact mul_assoc _ _ _
        change ∫ q, integrand (z • f) q ∂measure = _
        rw [hSmul]
        exact integral_smul z (integrand f) }
  let B : ℝ := max (∫ q, bound q ∂measure) 1
  have hB : 0 < B := zero_lt_one.trans_le (le_max_right _ _)
  have hnorm (f : V) : ‖operator f‖ ≤ B * ‖weighted f‖ := calc
    _ ≤ ∫ q, ‖integrand f q‖ ∂measure := norm_integral_le_integral_norm _
    _ ≤ ∫ q, ‖weighted f‖ * bound q ∂measure :=
      integral_mono_ae (hIntegrable f).norm (hbound.const_mul _) (hdom f)
    _ ≤ B * ‖weighted f‖ := by
      rw [integral_const_mul, mul_comm B]
      exact mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg _)
  have hdContinuous : Continuous weighted :=
    continuous_iff_le_induced.mpr (iInf_le _ (1 : AdelicEnvelopingAlgebra F G hsmooth))
  refine { operator with cont := continuous_iff_continuousAt.mpr (fun f => ?_) }
  change Tendsto operator (𝓝 f) (𝓝 (operator f))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hnear : ∀ᶠ y in 𝓝 f, dist (weighted y) (weighted f) < ε / B :=
    Metric.tendsto_nhds.mp hdContinuous.continuousAt _ (div_pos hε hB)
  filter_upwards [hnear] with y hy
  rw [dist_eq_norm] at hy ⊢
  rw [← map_sub]
  calc
    _ ≤ B * ‖weighted (y - f)‖ := hnorm _
    _ < B * (ε / B) := by rw [hdSub]; exact mul_lt_mul_of_pos_left hy hB
    _ = ε := by rw [← mul_div_assoc, mul_div_cancel_left₀ _ hB.ne']

@[simp]
theorem normOnePairingEvaluation_apply (f : V) :
    normOnePairingEvaluation F G M rho hsmooth hcalc hN hrho R L j ψ hψ g
        hcont bound hbound hrep f =
      ∫ q, valAt f (AdelicGroupPoints.map F M G j (Quotient.out q : normOneSubgroup F M).val * g) *
        starRingEnd ℂ (ψ (Quotient.out q : normOneSubgroup F M).val)
        ∂normOneRationalQuotientHaarMeasure F M := by
  change (∫ q, normOnePairingIntegrand F G M rho hsmooth hcalc hN hrho R L j ψ hψ g f q
    ∂normOneRationalQuotientHaarMeasure F M) = _
  congr 1
  funext q
  exact congrArg (normOnePairingIntegrand F G M rho hsmooth hcalc hN hrho R L j ψ hψ g f)
    (Quotient.out_eq q).symm

end Langlands.Automorphic.GroupSchemeFunctions.UniformGrowthFrechetSpace
