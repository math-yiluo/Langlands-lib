import Langlands.Automorphic.GroupSchemeConstantTerm
import Langlands.Automorphic.GroupSchemeUniformGrowthFrechet
import Langlands.Global.AdelicEisensteinConstantTermStatement
import Langlands.Global.AdelicLeviFiniteVolume
import Langlands.Global.AdelicRepresentationHeightPropernessProof

/-! # Constant-term evaluation in the uniform moderate growth topology -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Filter MeasureTheory Set
open scoped CategoryTheory.MonObj ENNReal Topology

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions.UniformGrowthFrechetSpace

open Langlands.Global Langlands.GroupScheme

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (hN : 0 < N) (hrho : IsClosedSubgroup rho) (R : ℝ)
  (L : Subgroup (FiniteAdelicGroupPoints F G))

local notation "V" => UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L

omit [IsAffine G.X.left] in
include hN in
private theorem continuous_weight :
    Continuous (fun x : AdelicGroupPoints F G =>
      RepresentationGrowth.adelicSourceNorm F G rho x ^ R) := by
  let scale : ℝ := (N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult)
  have hscale : scale ≠ 0 := (pow_pos (by exact_mod_cast hN) _).ne'
  have hSource : (RepresentationGrowth.adelicSourceNorm F G rho) =
      (fun x => RepresentationGrowth.adelicHeight F G rho x / scale) := by
    funext x
    rw [RepresentationGrowth.adelicHeight_eq_scalar_mul_sourceNorm]
    exact (mul_div_cancel_left₀ _ hscale).symm
  rw [hSource]
  exact ((RepresentationGrowth.continuous_adelicHeight F G rho hN).div_const scale).rpow_const
    (fun x => Or.inl (by rw [← congrFun hSource x]; exact
      (RepresentationGrowth.adelicSourceNorm_pos F G rho hN x).ne'))

variable [LocallyOfFiniteType G.X.hom]
  {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffine H.X.left]
  (j : H ⟶ G) [IsClosedImmersion j.hom.hom.left]
  [CompactSpace (AdelicSubgroupPoints.RationalQuotient F G (SubgroupFunctor.range j))]

/-- Averaging over the compact rational quotient of the actual subgroup
and evaluating at an adelic argument is continuous linear. -/
def constantTermEvaluation (g : AdelicGroupPoints F G) : V →L[ℂ] ℂ := by
  let U := SubgroupFunctor.range j
  let A := AdelicSubgroupPoints.adelicPoints F G U
  let Γ := AdelicSubgroupPoints.rationalSubgroup F G U
  let hClosed : IsClosed (A : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let : LocallyCompactSpace A := hClosed.locallyCompactSpace
  let : BorelSpace (AdelicSubgroupPoints.RationalQuotient F G U) :=
    AdelicSubgroupPoints.rationalQuotientBorelSpace F G U
  let measure := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G U
  let : IsProbabilityMeasure measure :=
    AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G U
  let forget (f : V) : ContinuousRationalFunctions F G :=
    (f : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).val.val
  have hvalue (f : V) : AdelicGroupPoints.subgroupConstantTerm F j
      (toFun F G rho hsmooth hcalc hN hrho R L f) g = constantTerm F G U measure (forget f) g := by
    unfold AdelicGroupPoints.subgroupConstantTerm constantTerm
    congr 1
    funext x
    have hx : LeftCosetSpace.mk Γ (Quotient.out x) = x := Quotient.out_eq x
    symm
    calc
      _ = constantTermIntegrand F G U (forget f) g (LeftCosetSpace.mk Γ (Quotient.out x)) :=
        congrArg _ hx.symm
      _ = _ := rfl
  have hIntegrable (f : V) : HasConvergentConstantTerm F G U measure (forget f) :=
    fun x => (continuous_constantTermIntegrand F G U (forget f) x).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  let operator : V →ₗ[ℂ] ℂ :=
    { toFun := fun f => AdelicGroupPoints.subgroupConstantTerm F j
        (toFun F G rho hsmooth hcalc hN hrho R L f) g
      map_add' := by
        intro f h
        simp only [hvalue]
        exact constantTerm_add F G U measure (forget f) (forget h)
          (hIntegrable f) (hIntegrable h) g
      map_smul' := by
        intro z f
        simp only [hvalue]
        exact constantTerm_smul F G U measure z (forget f) g }
  let weighted := weightedDerivative F G rho hsmooth hcalc hN hrho R L
    (1 : AdelicEnvelopingAlgebra F G hsmooth)
  let weight (x : AdelicGroupPoints F G) := RepresentationGrowth.adelicSourceNorm F G rho x ^ R
  have hweight (x : AdelicGroupPoints F G) : 0 < weight x :=
    Real.rpow_pos_of_pos (RepresentationGrowth.adelicSourceNorm_pos F G rho hN x) R
  have hdValue (f : V) (x : AdelicGroupPoints F G) :
      weighted f x = evaluate F G (forget f) x * ((weight x : ℝ) : ℂ)⁻¹ := by
    change evaluate F G (adelicEnvelopingAction F G hsmooth hcalc 1
        (f : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).val).val x *
        ((weight x : ℝ) : ℂ)⁻¹ = _
    rw [map_one, Module.End.one_apply]
  have hdSub (f h : V) : weighted (f - h) = weighted f - weighted h := by
    apply Subtype.ext
    funext x
    change weighted (f - h) x = weighted f x - weighted h x
    rw [hdValue, hdValue, hdValue]
    rw [sub_eq_add_neg f h, ← neg_one_smul ℂ h]
    change (evaluate F G (forget f) x + (-1 : ℂ) * evaluate F G (forget h) x) * _ = _
    ring
  have hdBound (f : V) (x : AdelicGroupPoints F G) :
      ‖evaluate F G (forget f) x‖ ≤ ‖weighted f‖ * weight x := by
    have hz := lp.norm_apply_le_norm ENNReal.top_ne_zero (weighted f) x
    rw [hdValue, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hweight x),
      ← div_eq_mul_inv] at hz
    exact (div_le_iff₀ (hweight x)).mp hz
  refine { operator with cont := ?_ }
  obtain ⟨C, hC, hcover⟩ := LeftCosetSpace.exists_isCompact_cover Γ
  obtain ⟨bound, hbound⟩ := (hC.image ((continuous_weight F G rho hN R).comp
    (continuous_subtype_val.mul (continuous_const (y := g))))).bddAbove
  let B := max bound 1
  have hB : 0 < B := zero_lt_one.trans_le (le_max_right _ _)
  have hnorm (f : V) : ‖operator f‖ ≤ B * ‖weighted f‖ := by
    change ‖AdelicGroupPoints.subgroupConstantTerm F j
      (toFun F G rho hsmooth hcalc hN hrho R L f) g‖ ≤ _
    rw [hvalue, constantTerm]
    have hdom : ∀ᵐ q ∂measure, ‖constantTermIntegrand F G U (forget f) g q‖ ≤ B * ‖weighted f‖ :=
      Filter.Eventually.of_forall (by
        intro q
        obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective Γ q
        obtain ⟨p, hp, hx⟩ := hcover x
        have hq : LeftCosetSpace.mk Γ (p * x) = LeftCosetSpace.mk Γ x :=
          LeftCosetSpace.mk_subgroup_mul Γ ⟨p, hp⟩ x
        rw [← hq, constantTermIntegrand_mk]
        have hbx : weight ((↑(p * x) : AdelicGroupPoints F G) * g) ≤ bound :=
          hbound ⟨p * x, hx, rfl⟩
        exact (hdBound f _).trans <|
          (mul_le_mul_of_nonneg_left (hbx.trans (le_max_left _ _)) (norm_nonneg _)).trans_eq
            (mul_comm _ _))
    exact (norm_integral_le_of_norm_le_const hdom).trans_eq (by simp [Measure.real_def])
  have hdContinuous : Continuous weighted :=
    continuous_iff_le_induced.mpr (iInf_le _ (1 : AdelicEnvelopingAlgebra F G hsmooth))
  apply continuous_iff_continuousAt.mpr
  intro f
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

@[simp] theorem constantTermEvaluation_apply (g : AdelicGroupPoints F G) (f : V) :
    constantTermEvaluation F G rho hsmooth hcalc hN hrho R L j g f =
      AdelicGroupPoints.subgroupConstantTerm F j (toFun F G rho hsmooth hcalc hN hrho R L f) g :=
  rfl

end Langlands.Automorphic.GroupSchemeFunctions.UniformGrowthFrechetSpace
