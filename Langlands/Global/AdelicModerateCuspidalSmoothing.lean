import Langlands.Global.AdelicNormOneCuspidalSeparationStatement
import Langlands.Global.AdelicRightConvolutionDifferentiation
import Langlands.Global.AdelicMaximalUnipotentDecay
import Langlands.Global.AdelicCuspidalProductVanishing
import Mathlib.MeasureTheory.Integral.Prod

/-! # Compact right smoothing of continuous moderate cuspidal functions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
open InfiniteAdelicGroupPoints AdelicSubgroupPoints RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local notation "A" => AdelicGroupPoints F G
local notation "dg" => (Measure.haar : Measure A)
local notation "R" => rightConvolution F G

/-- A compactly supported continuous kernel preserves the polynomial exponent
of a height bound. -/
theorem norm_rightConvolution_le_of_height_bound {N : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hN : 0 < N) {h f : A → ℂ} (hh : Continuous h) (hSupp : HasCompactSupport h)
    {C r : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r)
    (hf : ∀ x, ‖f x‖ ≤ C * adelicHeight F G rho x ^ r) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ x, ‖R h f x‖ ≤ C' * adelicHeight F G rho x ^ r := by
  let H := adelicHeight F G rho
  have hH₀ (x : A) : 0 ≤ H x := zero_le_one.trans (one_le_adelicHeight F G rho hN x)
  obtain ⟨B, hB⟩ := (hSupp.image (continuous_adelicHeight F G rho hN)).bddAbove
  let B' := max 0 B
  have hB' : 0 ≤ B' := le_max_left _ _
  have hh1 : Integrable (fun a : A => ‖h a‖) dg := hh.norm.integrable_of_hasCompactSupport hSupp.norm
  refine ⟨C * B' ^ r * (∫ a, ‖h a‖ ∂dg), by positivity, fun x => ?_⟩
  calc
    ‖R h f x‖ ≤ ∫ a, (C * B' ^ r * H x ^ r) * ‖h a‖ ∂dg := by
      apply norm_integral_le_of_norm_le (hh1.const_mul _)
      refine Filter.Eventually.of_forall fun a => ?_
      rw [norm_mul, mul_comm (C * B' ^ r * H x ^ r)]
      by_cases ha : a ∈ tsupport h
      · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        have haB : H a ≤ B' := (hB ⟨a, ha, rfl⟩).trans (le_max_right _ _)
        have hx : H (x * a) ≤ B' * H x := by
          rw [mul_comm B']
          exact (adelicHeight_mul_le F G rho hN _ _).trans (mul_le_mul_of_nonneg_left haB (hH₀ _))
        calc
          ‖f (x * a)‖ ≤ C * H (x * a) ^ r := hf _
          _ ≤ C * (B' * H x) ^ r :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hH₀ _) hx hr) hC
          _ = C * B' ^ r * H x ^ r := by rw [Real.mul_rpow hB' (hH₀ x), mul_assoc]
      · simp [image_eq_zero_of_notMem_tsupport ha]
    _ = _ := by rw [integral_const_mul]; ring

/-- Compact right convolution preserves any left invariance of the input. -/
theorem isLeftInvariantUnder_rightConvolution {Γ : Subgroup A} {h f : A → ℂ}
    (hInv : IsLeftInvariantUnder F G Γ f) : IsLeftInvariantUnder F G Γ (R h f) := by
  intro t ht x
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun a => ?_
  simp only [mul_assoc, hInv t ht]

section Period

variable {U : GroupScheme (Spec (CommRingCat.of F))} [IsAffine U.X.left]
  (j : U ⟶ G) [IsClosedImmersion j.hom.hom.left]

local notation "V" => SubgroupFunctor.range j
local notation "Uₐ" => adelicPoints F G V
local notation "Γ" => AdelicSubgroupPoints.rationalSubgroup F G V
local notation "Q" => AdelicSubgroupPoints.RationalQuotient F G V
local notation "du" => normalizedRationalQuotientHaarMeasure F G V

/-- A continuous compact right convolution commutes with each compact
radical average on a continuous rational-invariant function. -/
theorem subgroupConstantTerm_rightConvolution_apply [CompactSpace Q]
    {h f : A → ℂ} (hh : Continuous h) (hSupp : HasCompactSupport h) (hf : Continuous f)
    (hInv : IsLeftInvariantUnder F G (AdelicGroupPoints.rationalSubgroup F G) f) (g : A) :
    subgroupConstantTerm F j (R h f) g = R h (subgroupConstantTerm F j f) g := by
  let : IsClosed (Uₐ : Set A) := isClosed_adelicPoints_range F G j
  let : BorelSpace Q := AdelicSubgroupPoints.rationalQuotientBorelSpace F G V
  let : IsProbabilityMeasure du := normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G V
  let fU (a : A) : Q → ℂ := LeftCosetSpace.lift Γ (fun u : Uₐ => f (u.val * (g * a))) (fun r u => by
    change f ((r.val.val * u.val) * (g * a)) = f (u.val * (g * a))
    rw [mul_assoc]
    exact hInv _ (rationalImage_le_rationalSubgroup j ((mem_rationalSubgroup_range_iff j r.val).mp r.2)) _)
  let φ (q : Q) (a : A) : ℂ := h a * fU a q
  have hcont : Continuous (Function.uncurry φ) := by
    rw [← ((LeftCosetSpace.isOpenQuotientMap_mk Γ).prodMap IsOpenQuotientMap.id).continuous_comp_iff]
    change Continuous (fun p : Uₐ × A => h p.2 * f (p.1.val * (g * p.2)))
    exact (hh.comp continuous_snd).mul
      (hf.comp ((continuous_subtype_val.comp continuous_fst).mul (continuous_const.mul continuous_snd)))
  have hcs : HasCompactSupport (Function.uncurry φ) := by
    apply (isCompact_univ.prod hSupp).of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_univ.prod (isClosed_tsupport h))
    rintro ⟨q, a⟩ ha
    refine ⟨Set.mem_univ _, ?_⟩
    by_contra han
    exact ha (by change h a * fU a q = 0; rw [image_eq_zero_of_notMem_tsupport han, zero_mul])
  have hφ (q : Q) (a : A) : φ q a = h a * f ((Quotient.out q : Uₐ).val * (g * a)) :=
    (congrArg (fun x => h a * fU a x) (Quotient.out_eq q)).symm
  calc
    subgroupConstantTerm F j (R h f) g = ∫ q : Q, (∫ a, φ q a ∂dg) ∂du := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun q => ?_
      change (∫ a, h a * f (((Quotient.out q : Uₐ).val * g) * a) ∂dg) = _
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun a => by simp only [hφ, mul_assoc]
    _ = ∫ a, (∫ q : Q, φ q a ∂du) ∂dg := integral_integral_swap_of_hasCompactSupport hcont hcs
    _ = R h (subgroupConstantTerm F j f) g := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun a => ?_
      change (∫ q : Q, φ q a ∂du) = h a * (∫ q : Q, f ((Quotient.out q : Uₐ).val * (g * a)) ∂du)
      simp_rw [hφ, integral_const_mul]

end Period

/-- Compact right convolution preserves vanishing of the absolute proper
parabolic constant terms. -/
theorem hasZeroProperParabolicConstantTerms_rightConvolution {h f : A → ℂ}
    (hh : Continuous h) (hSupp : HasCompactSupport h) (hf : Continuous f)
    (hInv : IsLeftInvariantUnder F G (AdelicGroupPoints.rationalSubgroup F G) f)
    (hCuspidal : HasZeroProperParabolicConstantTerms f) : HasZeroProperParabolicConstantTerms (R h f) := by
  intro P U p r _ _ hp hr hProper
  let : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G (SubgroupFunctor.range (r ≫ p))) :=
    compactSpace_rationalQuotient_range_unipotent F (r ≫ p) hr.1.smooth hr.1.connectedSpace hr.1.isUnipotent
  funext g
  rw [subgroupConstantTerm_rightConvolution_apply (r ≫ p) hh hSupp hf hInv, hCuspidal P U p r hp hr hProper]
  simp [rightConvolution]

variable {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)

/-- A word of archimedean orbit derivatives of right convolution is again
right convolution, with a differentiated compact test kernel. -/
theorem exists_rightConvolution_directionalKernel {h f : A → ℂ}
    (hh : IsAdelicTestFunction F G h) (hf : Continuous f) (s : List (smoothModel F d)) :
    ∃ k : A → ℂ, IsAdelicTestFunction F G k ∧ tsupport k ⊆ tsupport h ∧
      adelicIteratedDirectionalValue hsmooth s (R h f) = R k f := by
  induction s with
  | nil => exact ⟨h, hh, Set.Subset.rfl, adelicIteratedDirectionalValue_nil hsmooth _⟩
  | cons X s ih =>
    obtain ⟨k, hk, hks, heq⟩ := ih
    obtain ⟨hk', hk's⟩ := rightConvolutionKernelDerivative_isTestFunction hsmooth X hk
    refine ⟨rightConvolutionKernelDerivative hsmooth X k, hk', hk's.trans hks, ?_⟩
    rw [adelicIteratedDirectionalValue_cons, heq]
    funext x
    rw [← pair_projections F G x, adelicDirectionalValue_pair]
    exact (adelicRightConvolutionDifferentiation F G d hsmooth k f hk hf.measurable
      hf.locallyIntegrable).2.2 X _ _

/-- A compact smooth test kernel gives a continuous moderate cuspidal input
smooth finite-level output with one polynomial height exponent for all
archimedean orbit derivatives. -/
def AdelicModerateCuspidalSmoothingStatement : Prop :=
  ∀ {N : ℕ} (rho : MatrixRepresentation G (Fin N)), 0 < N →
    ∀ (h f : A → ℂ), IsAdelicTestFunction F G h → Continuous f →
      IsLeftInvariantUnder F G (AdelicGroupPoints.rationalSubgroup F G) f →
      HasModerateGrowthFunction F G rho f → HasZeroProperParabolicConstantTerms f →
      IsAdelicSmoothFunction F G (R h f) ∧
      IsLeftInvariantUnder F G (AdelicGroupPoints.rationalSubgroup F G) (R h f) ∧
      HasZeroProperParabolicConstantTerms (R h f) ∧
      ∃ r : ℝ, 0 ≤ r ∧ ∀ s : List (smoothModel F d), ∃ C : ℝ, 0 ≤ C ∧
        ∀ x, ‖adelicIteratedDirectionalValue hsmooth s (R h f) x‖ ≤ C * adelicHeight F G rho x ^ r

theorem adelicModerateCuspidalSmoothing : AdelicModerateCuspidalSmoothingStatement hsmooth := by
  intro N rho hN h f hh hf hInv hgrowth hCusp
  refine ⟨(adelicRightConvolutionDifferentiation F G d hsmooth h f hh hf.measurable
    hf.locallyIntegrable).2.1, isLeftInvariantUnder_rightConvolution hInv,
    hasZeroProperParabolicConstantTerms_rightConvolution hh.1.1 hh.2.1 hf hInv hCusp, ?_⟩
  obtain ⟨C, r, hC, hr, hg⟩ := (hasModerateGrowthFunction_iff_hasHeightGrowth hN f).mp hgrowth
  refine ⟨r, hr, fun s => ?_⟩
  obtain ⟨k, hk, _, heq⟩ := exists_rightConvolution_directionalKernel hsmooth hh hf s
  rw [heq]
  exact norm_rightConvolution_le_of_height_bound rho hN hk.1.1 hk.2.1 hC hr hg

end Langlands.Global.AdelicGroupPoints
