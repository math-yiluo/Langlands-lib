import Langlands.Automorphic.GroupSchemeUniformGrowthConstantTerm
import Langlands.Automorphic.GroupSchemeUniformGrowthFrechetInstances
import Langlands.Global.AdelicCompactConstantTermCovariance
import Langlands.Global.AdelicFiniteVolumeProof
import Langlands.Global.AdelicLeadingCuspidalComponents
import Langlands.Global.AdelicNormalizerConjugation
import Langlands.Global.EisensteinConstantTerm.Points

/-! # Uniform-growth evaluation of a constant term against a Levi cusp test -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Filter MeasureTheory
open scoped CategoryTheory.MonObj ENNReal Topology

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions.UniformGrowthFrechetSpace

open Langlands.Global Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (hN : 0 < N) (hrho : IsClosedSubgroup rho) (R : ℝ)
  (L : Subgroup (FiniteAdelicGroupPoints F G))
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)

local notation "Space" => UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L
local notation "value" => toFun F G rho hsmooth hcalc hN hrho R L
local notation "M" => fam.M J
local notation "U" => fam.U J
local notation "P" => fam.P J
local notation "jU" => fam.iU J ≫ fam.p J
local notation "jM" => fam.l J ≫ fam.p J
local notation "V" => SubgroupFunctor.range (fam.iU J ≫ fam.p J)
local notation "Weight" => fun x => RepresentationGrowth.adelicSourceNorm F G rho x ^ R
local notation "MeasureM" => normOneRationalQuotientHaarMeasure F (fam.M J)
local notation "MeasureU" => AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G V

/-- Along the norm-one Levi quotient a fixed test has an integrable
representative bound for the weighted integrand, uniformly over any compact
set of left translates in the constant-term averaging. -/
def HasConstantTermLeviPairingBound (g : AdelicGroupPoints F G)
    (test : AdelicGroupPoints F (fam.M J) → ℂ) : Prop :=
  ∀ C : Set (AdelicGroupPoints F G), IsCompact C →
    ∃ bound : NormOneRationalQuotient F M → ℝ, Integrable bound MeasureM ∧
      ∀ᵐ q ∂MeasureM, ∃ m : normOneSubgroup F M,
        LeftCosetSpace.mk (rationalNormOneSubgroup F M) m = q ∧
        ∀ u ∈ C, Weight (u * (map F M G jM m.val * g)) * ‖test m.val‖ ≤ bound q

/-- Bounds of every nonnegative polynomial weight on representatives
give the integrable bound, with compact left translates and a fixed
external right translate. -/
theorem hasConstantTermLeviPairingBound_of_rapid_representatives
    (hPositive : 0 < N) (g : AdelicGroupPoints F G) (test : AdelicGroupPoints F (fam.M J) → ℂ)
    (hdecay : ∀ s : ℝ, 0 ≤ s → ∃ b : ℝ, ∀ q : NormOneRationalQuotient F M,
      ∃ m : normOneSubgroup F M,
        LeftCosetSpace.mk (rationalNormOneSubgroup F M) m = q ∧
        RepresentationGrowth.adelicHeight F G rho (map F M G jM m.val) ^ s *
          ‖test m.val‖ ≤ b) :
    HasConstantTermLeviPairingBound F G rho R fam J g test := by
  intro C hC
  let H := RepresentationGrowth.adelicHeight F G rho
  let scale : ℝ := (N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult)
  have hScale : 0 < scale := pow_pos (Nat.cast_pos.mpr hPositive) _
  have hH (x : AdelicGroupPoints F G) : 1 ≤ H x :=
    RepresentationGrowth.one_le_adelicHeight F G rho hPositive x
  have hWeight (x : AdelicGroupPoints F G) : Weight x = H x ^ R / scale ^ R := by
    have hsource : RepresentationGrowth.adelicSourceNorm F G rho x = H x / scale := by
      change _ = RepresentationGrowth.adelicHeight F G rho x / scale
      rw [RepresentationGrowth.adelicHeight_eq_scalar_mul_sourceNorm]
      exact (mul_div_cancel_left₀ _ hScale.ne').symm
    change RepresentationGrowth.adelicSourceNorm F G rho x ^ R = _
    rw [hsource, Real.div_rpow (zero_le_one.trans (hH x)) hScale.le]
  obtain ⟨D, hD⟩ := (hC.image (RepresentationGrowth.continuous_adelicHeight F G rho hPositive)).bddAbove
  let B := max D 1 * H g
  have hB : 0 < B := mul_pos (zero_lt_one.trans_le (le_max_right _ _))
    (zero_lt_one.trans_le (hH g))
  have hmul {a : AdelicGroupPoints F G} (ha : a ∈ C) (m : AdelicGroupPoints F G) :
      H (a * (m * g)) ≤ B * H m := by
    have hHa : H a ≤ max D 1 := (hD ⟨a, ha, rfl⟩).trans (le_max_left _ _)
    calc
      _ ≤ H a * H (m * g) := RepresentationGrowth.adelicHeight_mul_le F G rho hPositive _ _
      _ ≤ max D 1 * (H m * H g) := mul_le_mul hHa
        (RepresentationGrowth.adelicHeight_mul_le F G rho hPositive _ _)
        (zero_le_one.trans (hH _)) (zero_le_one.trans (le_max_right _ _))
      _ = B * H m := by
        dsimp only [B]
        ring
  let s := max R 0
  have hs : 0 ≤ s := le_max_right _ _
  have hScaleR : 0 < scale ^ R := Real.rpow_pos_of_pos hScale _
  let factor := B ^ s / scale ^ R
  have hFactor : 0 ≤ factor := div_nonneg (Real.rpow_nonneg hB.le _) hScaleR.le
  obtain ⟨b, hb⟩ := hdecay s hs
  let : IsFiniteMeasure MeasureM :=
    connectedReductiveFiniteVolume F M (fam.isCompatible J).levi.isConnectedReductive
  refine ⟨fun _ => factor * b, integrable_const _, Filter.Eventually.of_forall (fun q => ?_)⟩
  obtain ⟨m, hm, hq⟩ := hb q
  refine ⟨m, hm, fun a ha => ?_⟩
  let mG := map F M G jM m.val
  let x := a * (mG * g)
  have hW : Weight x ≤ factor * H mG ^ s := by
    rw [hWeight]
    calc
      _ ≤ (H x) ^ s / scale ^ R := div_le_div_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le (hH x) (le_max_left _ _)) hScaleR.le
      _ ≤ (B * H mG) ^ s / scale ^ R := div_le_div_of_nonneg_right
        (Real.rpow_le_rpow (zero_le_one.trans (hH x)) (hmul ha mG) hs) hScaleR.le
      _ = factor * H mG ^ s := by
        rw [Real.mul_rpow hB.le (zero_le_one.trans (hH mG))]
        simp only [factor, div_mul_eq_mul_div]
  exact (mul_le_mul_of_nonneg_right hW (norm_nonneg _)).trans (by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hq hFactor)

/-- The actual constant-term pairing is continuous linear in the ambient
uniform-growth function under an integrable weighted bound on Levi tests. -/
def constantTermLeviPairingEvaluation (g : AdelicGroupPoints F G)
    (test : AdelicGroupPoints F (fam.M J) → ℂ)
    (hTest : IsLeftInvariantUnder F M (rationalSubgroup F M) test)
    (hTestCont : Continuous test)
    (hbound : HasConstantTermLeviPairingBound F G rho R fam J g test) :
    Space →L[ℂ] ℂ := by
  let hClosed : IsClosed (AdelicSubgroupPoints.adelicPoints F G V : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G jU
  let : IsClosed (AdelicSubgroupPoints.adelicPoints F G V : Set (AdelicGroupPoints F G)) := hClosed
  let : LocallyCompactSpace (AdelicSubgroupPoints.adelicPoints F G V) := hClosed.locallyCompactSpace
  let : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G V) :=
    AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F jU
      (fam.isUnipotentRadical J).1.smooth (fam.isUnipotentRadical J).1.connectedSpace
      (fam.isUnipotentRadical J).1.isUnipotent
  let : IsProbabilityMeasure MeasureU :=
    AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G V
  let Γ := rationalNormOneSubgroup F M
  let ΓU := AdelicSubgroupPoints.rationalSubgroup F G V
  let forget (f : Space) : ContinuousRationalFunctions F G :=
    (f : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).val.val
  let ct (x : AdelicGroupPoints F G) :=
    constantTermEvaluation F G rho hsmooth hcalc hN hrho R L jU x
  let I (f : Space) : NormOneRationalQuotient F M → ℂ :=
    fam.leviPairingIntegrand J (fam.constantTerm J (value f)) g test
  let descended (f : Space) :=
    LeftCosetSpace.lift Γ
      (fun m : normOneSubgroup F M => ct (map F M G jM m.val * g) f * starRingEnd ℂ (test m.val))
      (by
        rintro ⟨_, x, rfl⟩ m
        let z := (basePointEquiv (F := F) (G := M)).symm x
        have mapRat : map F M G jM (rational F M x) =
            innerAdelicPoint F G ((z ≫ (fam.l J).hom.hom) ≫ (fam.p J).hom.hom) := by
          have hBase : rational F G (basePointEquiv ((z ≫ (fam.l J).hom.hom) ≫ (fam.p J).hom.hom)) =
              innerAdelicPoint F G ((z ≫ (fam.l J).hom.hom) ≫ (fam.p J).hom.hom) :=
            rational_basePointEquiv _
          rw [← hBase]
          rw [basePointEquiv_comp, basePointEquiv_comp, ← map_rational, ← map_rational,
            map_comp_apply_of_hom]
          exact congrArg (fun y => map F M G jM (rational F M y)) (MulEquiv.apply_symm_apply _ x).symm
        change ct (map F M G jM (rational F M x * m.val) * g) f *
          starRingEnd ℂ (test (rational F M x * m.val)) = _
        rw [map_mul, mul_assoc, mapRat, hTest _ ⟨x, rfl⟩ m.val]
        exact congrArg (fun z' : ℂ => z' * starRingEnd ℂ (test m.val))
          (subgroupConstantTerm_rational_parabolic_mul (fam.p J) (fam.iU J)
            (fam.isUnipotentRadical J) (forget f) (z ≫ (fam.l J).hom.hom) _))
  have hDesc (f : Space) : I f = descended f := by
    funext q
    exact congrArg (descended f) (Quotient.out_eq q)
  have hcont (f : Space) : Continuous (descended f) := by
    apply (LeftCosetSpace.continuous_iff Γ).mpr
    change Continuous (fun m : normOneSubgroup F M =>
      subgroupConstantTerm F jU (evaluate F G (forget f)) (map F M G jM m.val * g) *
        starRingEnd ℂ (test m.val))
    exact ((continuous_subgroupConstantTerm jU (forget f)).comp
      (((map F M G jM).continuous.comp continuous_subtype_val).mul continuous_const)).mul
      (Complex.continuous_conj.comp (hTestCont.comp continuous_subtype_val))
  let weighted := weightedDerivativeCLM F G rho hsmooth hcalc hN hrho R L 1
  have hpoint (f : Space) (x : AdelicGroupPoints F G) :
      ‖value f x‖ ≤ ‖weighted f‖ * Weight x := by
    have hpos : 0 < Weight x :=
      Real.rpow_pos_of_pos (RepresentationGrowth.adelicSourceNorm_pos F G rho hN x) R
    have h := lp.norm_apply_le_norm ENNReal.top_ne_zero (weighted f) x
    change ‖weightedDerivative F G rho hsmooth hcalc hN hrho R L 1 f x‖ ≤ _ at h
    rw [weightedDerivative_one_apply, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hpos, ← div_eq_mul_inv] at h
    exact (div_le_iff₀ hpos).mp h
  let cover := LeftCosetSpace.exists_isCompact_cover ΓU
  let C := Classical.choose cover
  have hC : IsCompact C := (Classical.choose_spec cover).1
  have hCover := (Classical.choose_spec cover).2
  let majorant := hbound (Subtype.val '' C) (hC.image continuous_subtype_val)
  let bound := Classical.choose majorant
  have hIntegrable : Integrable bound MeasureM := (Classical.choose_spec majorant).1
  have hRep := (Classical.choose_spec majorant).2
  have hdom (f : Space) : ∀ᵐ q ∂MeasureM, ‖I f q‖ ≤ ‖weighted f‖ * bound q := by
    filter_upwards [hRep] with q hq
    obtain ⟨m, hm, hbm⟩ := hq
    rw [hDesc, ← hm]
    change ‖ct (map F M G jM m.val * g) f * starRingEnd ℂ (test m.val)‖ ≤ _
    rw [hm]
    let x := map F M G jM m.val * g
    change ‖subgroupConstantTerm F jU (evaluate F G (forget f)) x *
      starRingEnd ℂ (test m.val)‖ ≤ _
    rw [subgroupConstantTerm_eq_continuousConstantTerm jU (forget f) x]
    unfold GroupSchemeFunctions.constantTerm
    rw [← integral_mul_const]
    have hCT : ∀ᵐ r ∂MeasureU,
        ‖constantTermIntegrand F G V (forget f) x r * starRingEnd ℂ (test m.val)‖ ≤
          ‖weighted f‖ * bound q := by
      refine Filter.Eventually.of_forall fun r => ?_
      obtain ⟨u, rfl⟩ := LeftCosetSpace.mk_surjective ΓU r
      obtain ⟨a, ha, hC'⟩ := hCover u
      rw [← LeftCosetSpace.mk_subgroup_mul ΓU ⟨a, ha⟩ u, constantTermIntegrand_mk,
        norm_mul, Complex.norm_conj]
      exact (mul_le_mul_of_nonneg_right (hpoint f _) (norm_nonneg _)).trans (by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (hbm _ ⟨a * u, hC', rfl⟩) (norm_nonneg _))
    exact (norm_integral_le_of_norm_le_const hCT).trans_eq (by simp [Measure.real_def])
  have hint (f : Space) : Integrable (I f) MeasureM :=
    (hIntegrable.const_mul ‖weighted f‖).mono'
      ((hDesc f).symm ▸ (hcont f).aestronglyMeasurable) (hdom f)
  let operator : Space →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ q, I f q ∂MeasureM
      map_add' f h := by
        have hAdd : I (f + h) = I f + I h := by
          funext q
          change ct _ (f + h) * _ = ct _ f * _ + ct _ h * _
          rw [map_add, add_mul]
        change (∫ q, I (f + h) q ∂MeasureM) = _
        rw [hAdd]
        exact integral_add (hint f) (hint h)
      map_smul' c f := by
        have hSmul : I (c • f) = c • I f := by
          funext q
          change ct _ (c • f) * _ = c * (ct _ f * _)
          rw [map_smul, smul_eq_mul, mul_assoc]
        change (∫ q, I (c • f) q ∂MeasureM) = _
        rw [hSmul]
        exact integral_smul c (I f) }
  let B := max (∫ q, bound q ∂MeasureM) 1
  have hB : 0 < B := zero_lt_one.trans_le (le_max_right _ _)
  have hop (f : Space) : ‖operator f‖ ≤ B * ‖weighted f‖ := calc
    _ ≤ ∫ q, ‖I f q‖ ∂MeasureM := norm_integral_le_integral_norm _
    _ ≤ ∫ q, ‖weighted f‖ * bound q ∂MeasureM :=
      integral_mono_ae (hint f).norm (hIntegrable.const_mul _) (hdom f)
    _ ≤ B * ‖weighted f‖ := by
      rw [integral_const_mul, mul_comm B]
      exact mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg _)
  refine ⟨operator, continuous_of_continuousAt_zero operator ?_⟩
  change Tendsto operator (𝓝 0) (𝓝 (operator 0))
  rw [map_zero, Metric.tendsto_nhds]
  intro ε hε
  have hw : Tendsto weighted (𝓝 0) (𝓝 (weighted 0)) := weighted.continuous.continuousAt
  have hNear := Metric.tendsto_nhds.mp hw (ε / B) (div_pos hε hB)
  rw [map_zero] at hNear
  filter_upwards [hNear] with f hf
  rw [dist_zero_right] at hf ⊢
  calc
    _ ≤ B * ‖weighted f‖ := hop f
    _ < B * (ε / B) := mul_lt_mul_of_pos_left hf hB
    _ = ε := by rw [← mul_div_assoc, mul_div_cancel_left₀ _ hB.ne']

@[simp]
theorem constantTermLeviPairingEvaluation_apply (g : AdelicGroupPoints F G)
    (test : AdelicGroupPoints F (fam.M J) → ℂ)
    (hTest : IsLeftInvariantUnder F M (rationalSubgroup F M) test)
    (hTestCont : Continuous test)
    (hbound : HasConstantTermLeviPairingBound F G rho R fam J g test) (f : Space) :
    constantTermLeviPairingEvaluation F G rho hsmooth hcalc hN hrho R L fam J
        g test hTest hTestCont hbound f =
      fam.leviPairing J (fam.constantTerm J (value f)) g test :=
  rfl

end Langlands.Automorphic.GroupSchemeFunctions.UniformGrowthFrechetSpace
