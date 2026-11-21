import Langlands.Global.AdelicEisensteinConstantTermStatement
import Langlands.Global.AdelicRepresentationHeightPropernessProof
import Langlands.Automorphic.GroupSchemeConstantTermConsequences
import Langlands.Automorphic.GroupSchemeUniformGrowthFrechetInstances

/-! # Continuous evaluation of the adelic constant term

For a closed adelic subgroup with compact rational quotient, normalized
constant-term integration on a weighted growth stage has a pointwise bound
of the same exponent. In particular each evaluation is continuous and linear. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Filter
open scoped CategoryTheory.MonObj ENNReal Topology

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

private theorem compact_representatives {B : Type u} [Group B] [TopologicalSpace B]
    [IsTopologicalGroup B] [LocallyCompactSpace B] (Γ : Subgroup B)
    [CompactSpace (LeftCosetSpace Γ)] :
    ∃ K : Set B, IsCompact K ∧ ∀ q : LeftCosetSpace Γ, ∃ y ∈ K, LeftCosetSpace.mk Γ y = q := by
  classical
  choose K hKc hKn using fun b : B => exists_compact_mem_nhds b
  let V (b : B) : Set (LeftCosetSpace Γ) := LeftCosetSpace.mk Γ '' interior (K b)
  have ho : ∀ b, IsOpen (V b) := fun b =>
    (LeftCosetSpace.isOpenQuotientMap_mk Γ).isOpenMap _ isOpen_interior
  have hcover : (Set.univ : Set (LeftCosetSpace Γ)) ⊆ ⋃ b, V b := by
    intro q _
    obtain ⟨b, rfl⟩ := LeftCosetSpace.mk_surjective Γ q
    exact Set.mem_iUnion.mpr ⟨b, b, mem_interior_iff_mem_nhds.mpr (hKn b), rfl⟩
  obtain ⟨fin, hfin⟩ := isCompact_univ.elim_finite_subcover V ho hcover
  refine ⟨⋃ b ∈ fin, K b, fin.finite_toSet.isCompact_biUnion (fun b _ => hKc b), fun q => ?_⟩
  obtain ⟨b, hb, y, hy, rfl⟩ := Set.mem_iUnion₂.mp (hfin (Set.mem_univ q))
  exact ⟨y, Set.mem_iUnion₂.mpr ⟨b, hb, interior_subset hy⟩, rfl⟩

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) {N : ℕ}
  (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N)

local notation "Hgt" => RepresentationGrowth.adelicHeight F G rho
local notation "Nrm" => RepresentationGrowth.adelicSourceNorm F G rho

include hN in
private theorem sourceNorm_mul_le (x g : AdelicGroupPoints F G) :
    Nrm (x * g) ≤ Hgt x * Nrm g := by
  let C : ℝ := (N : ℝ) ^ (∑ v : InfinitePlace F, v.mult)
  have hC : 0 < C := pow_pos (by exact_mod_cast hN) _
  apply le_of_mul_le_mul_left _ hC
  calc
    C * Nrm (x * g) = Hgt (x * g) :=
      (RepresentationGrowth.adelicHeight_eq_scalar_mul_sourceNorm F G rho _).symm
    _ ≤ Hgt x * Hgt g := RepresentationGrowth.adelicHeight_mul_le F G rho hN x g
    _ = C * (Hgt x * Nrm g) := by
      rw [RepresentationGrowth.adelicHeight_eq_scalar_mul_sourceNorm F G rho g]
      change Hgt x * (C * Nrm g) = _
      ring

include hN in
private theorem sourceNorm_rpow_mul_le (R : ℝ) (x g : AdelicGroupPoints F G) :
    Nrm (x * g) ^ R ≤ Hgt x ^ |R| * Nrm g ^ R := by
  have hp (y) : 0 < Nrm y := RepresentationGrowth.adelicSourceNorm_pos F G rho hN y
  have hx : 0 < Hgt x := zero_lt_one.trans_le (RepresentationGrowth.one_le_adelicHeight F G rho hN x)
  by_cases hR : 0 ≤ R
  · rw [abs_of_nonneg hR, ← Real.mul_rpow hx.le (hp g).le]
    exact Real.rpow_le_rpow (hp _).le (sourceNorm_mul_le F G rho hN x g) hR
  · have hinv : Nrm g ≤ Hgt x * Nrm (x * g) := by
      simpa only [inv_mul_cancel_left, RepresentationGrowth.adelicHeight_inv] using
        sourceNorm_mul_le F G rho hN x⁻¹ (x * g)
    have hb := Real.rpow_le_rpow_of_nonpos (hp g) hinv (le_of_not_ge hR)
    rw [Real.mul_rpow hx.le (hp _).le] at hb
    rw [abs_of_nonpos (le_of_not_ge hR), Real.rpow_neg hx.le, ← div_eq_inv_mul]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hx R)).2 (by rwa [mul_comm])

variable [IsAffine G.X.left] {d : ℕ} (hrho : IsClosedSubgroup rho)
  (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (R : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F G))

local notation "𝔉" => UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L
local notation "value" => UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L
local notation "D₁" => weightedDerivativeCLM F G rho hsmooth hcalc hN hrho R L 1

/-- Forget the growth and level conditions and retain the continuous rational-invariant
function, as a linear map of carriers. -/
def uniformGrowthToContinuousRational : 𝔉 →ₗ[ℂ] ContinuousRationalFunctions F G where
  toFun v := (v : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).val.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem norm_value_le (v : 𝔉) (g : AdelicGroupPoints F G) :
    ‖value v g‖ ≤ ‖D₁ v‖ * Nrm g ^ R := by
  have hw := Real.rpow_pos_of_pos (RepresentationGrowth.adelicSourceNorm_pos F G rho hN g) R
  have hb := lp.norm_apply_le_norm ENNReal.top_ne_zero (D₁ v) g
  rw [weightedDerivativeCLM_apply, weightedDerivative_one_apply, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw, ← div_eq_mul_inv] at hb
  exact (div_le_iff₀ hw).1 hb

variable [LocallyOfFiniteType G.X.hom] (U : SubgroupFunctor G)
  [hU : IsClosed (AdelicSubgroupPoints.adelicPoints F G U : Set (AdelicGroupPoints F G))]
  [CompactSpace (AdelicSubgroupPoints.RationalQuotient F G U)]

local notation "Q" => AdelicSubgroupPoints.RationalQuotient F G U
local notation "dQ" => AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G U
local notation "asContinuous" => uniformGrowthToContinuousRational F G rho hN hrho hsmooth hcalc R L

/-- There is a single pointwise bound for the normalized constant term, at every ambient
adelic point, in terms of the order-zero input seminorm and the *same* exponent `R`. -/
theorem exists_norm_normalizedConstantTerm_le :
    ∃ C : ℝ, ∀ (v : 𝔉) (g : AdelicGroupPoints F G),
      ‖constantTerm F G U dQ (asContinuous v) g‖ ≤ C * ‖D₁ v‖ * Nrm g ^ R := by
  let : LocallyCompactSpace (AdelicSubgroupPoints.adelicPoints F G U) := hU.locallyCompactSpace
  obtain ⟨K, hK, hsurj⟩ := compact_representatives (AdelicSubgroupPoints.rationalSubgroup F G U)
  let b (x : AdelicSubgroupPoints.adelicPoints F G U) : ℝ := Hgt x.val ^ |R|
  have hb : Continuous b :=
    ((RepresentationGrowth.continuous_adelicHeight F G rho hN).comp continuous_subtype_val).rpow_const
      (fun _ => Or.inr (abs_nonneg R))
  obtain ⟨C, hC⟩ := hK.bddAbove_image hb.continuousOn
  refine ⟨C, fun v g => ?_⟩
  let := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G U
  unfold constantTerm
  refine (norm_integral_le_of_norm_le_const (C := C * ‖D₁ v‖ * Nrm g ^ R)
    (Eventually.of_forall fun q => ?_)).trans_eq (by simp)
  obtain ⟨y, hy, rfl⟩ := hsurj q
  rw [constantTermIntegrand_mk]
  change ‖value v (y.val * g)‖ ≤ _
  calc
    _ ≤ ‖D₁ v‖ * Nrm (y.val * g) ^ R :=
      norm_value_le F G rho hN hrho hsmooth hcalc R L v _
    _ ≤ ‖D₁ v‖ * (b y * Nrm g ^ R) :=
      mul_le_mul_of_nonneg_left (sourceNorm_rpow_mul_le F G rho hN R y.val g) (norm_nonneg _)
    _ = b y * ‖D₁ v‖ * Nrm g ^ R := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hC ⟨y, hy, rfl⟩) (norm_nonneg _))
      (Real.rpow_nonneg (RepresentationGrowth.adelicSourceNorm_pos F G rho hN g).le _)

private def normalizedConstantTermEvalLinearMap (g : AdelicGroupPoints F G) : 𝔉 →ₗ[ℂ] ℂ := by
  letI := AdelicSubgroupPoints.rationalQuotientBorelSpace F G U
  letI := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G U
  exact (LinearMap.proj g).comp ((compactConstantTermLinearMap F G U dQ).comp asContinuous)

/-- A continuous complex-linear form obtained by evaluating the normalized constant term
at a fixed adelic point. The integration is over the actual compact rational quotient. -/
def normalizedConstantTermEvalCLM (g : AdelicGroupPoints F G) : 𝔉 →L[ℂ] ℂ where
  toLinearMap := normalizedConstantTermEvalLinearMap F G rho hN hrho hsmooth hcalc R L U g
  cont := by
    refine continuous_of_tendsto_nhds_zero
      (normalizedConstantTermEvalLinearMap F G rho hN hrho hsmooth hcalc R L U g) ?_
    apply tendsto_zero_iff_norm_tendsto_zero.2
    obtain ⟨C, hC⟩ := exists_norm_normalizedConstantTerm_le F G rho hN hrho hsmooth hcalc R L U
    refine squeeze_zero (fun _ => norm_nonneg _) (fun v => hC v g) ?_
    let c := Nrm g ^ R
    let D := D₁
    have hc : Continuous (fun v : 𝔉 => C * ‖D v‖ * c) :=
      (continuous_const.mul D.continuous.norm).mul continuous_const
    simpa only [map_zero, norm_zero, mul_zero, zero_mul] using
      (hc.continuousAt (x := (0 : 𝔉))).tendsto

@[simp]
theorem normalizedConstantTermEvalCLM_apply (g : AdelicGroupPoints F G) (v : 𝔉) :
    normalizedConstantTermEvalCLM F G rho hN hrho hsmooth hcalc R L U g v =
      constantTerm F G U dQ (asContinuous v) g := rfl

variable {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffine H.X.left]
  (j : H ⟶ G) [IsClosedImmersion j.hom.hom.left]
  [CompactSpace (AdelicSubgroupPoints.RationalQuotient F G (SubgroupFunctor.range j))]

omit hU in
/-- The bundled evaluation for the `subgroupConstantTerm` used in the Eisenstein equations. -/
def subgroupConstantTermEvalCLM (g : AdelicGroupPoints F G) : 𝔉 →L[ℂ] ℂ :=
  letI := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  normalizedConstantTermEvalCLM F G rho hN hrho hsmooth hcalc R L (SubgroupFunctor.range j) g

omit hU in
@[simp]
theorem subgroupConstantTermEvalCLM_apply (g : AdelicGroupPoints F G) (v : 𝔉) :
    subgroupConstantTermEvalCLM F G rho hN hrho hsmooth hcalc R L j g v =
      AdelicGroupPoints.subgroupConstantTerm F j (value v) g := by
  let := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  rw [subgroupConstantTermEvalCLM, normalizedConstantTermEvalCLM_apply]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro q
  calc
    _ = constantTermIntegrand F G (SubgroupFunctor.range j) (asContinuous v) g
          (LeftCosetSpace.mk _ (Quotient.out q)) :=
      congrArg _ (Quotient.out_eq q).symm
    _ = _ := rfl

omit hU in
/-- The same pointwise estimate for the representative formula in the Eisenstein equations. -/
theorem exists_norm_subgroupConstantTerm_le :
    ∃ C : ℝ, ∀ (v : 𝔉) (g : AdelicGroupPoints F G),
      ‖AdelicGroupPoints.subgroupConstantTerm F j (value v) g‖ ≤ C * ‖D₁ v‖ * Nrm g ^ R := by
  let := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  obtain ⟨C, hC⟩ := exists_norm_normalizedConstantTerm_le F G rho hN hrho hsmooth hcalc R L
    (SubgroupFunctor.range j)
  refine ⟨C, fun v g => ?_⟩
  rw [← subgroupConstantTermEvalCLM_apply, subgroupConstantTermEvalCLM,
    normalizedConstantTermEvalCLM_apply]
  exact hC v g

end Langlands.Global
