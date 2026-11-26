import Langlands.Automorphic.GroupSchemePositiveQuotientL2Smoothing
import Langlands.Automorphic.GroupSchemeFullAEL2Integrated
import Langlands.Automorphic.GroupSchemeFullAEL2ContinuousCuspidality
import Langlands.Global.AdelicCompactConstantTermCovariance
import Langlands.Global.AdelicFullHeightRationalReduction
import Langlands.Global.AdelicNormOneCuspidalRapidDecay
import Langlands.GroupScheme.Rational.AffineGeometricUnipotentRadical
import Langlands.Analysis.HilbertSchmidtEvaluationProof
import Langlands.Analysis.HilbertSchmidtCompactProof
import Langlands.Global.ReductiveInfiniteAdelicManifold
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-! # Compact smooth convolution on the cuspidal Hilbert space -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Set
open scoped CategoryTheory.MonObj CompactlySupported Pointwise InnerProductSpace Classical

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global AdelicGroupPoints PositiveRealTorus RepresentationGrowth InfiniteAdelicGroupPoints
  Langlands.GroupScheme Langlands.Analysis.OperatorIdeals

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local notation "A" => AdelicGroupPoints F G

/-- Pointwise cuspidality in the canonical radical family gives the constant
term along any closed representative of a proper parabolic radical. -/
theorem hasZeroProperParabolicConstantTerms_of_normalized (hPD : ParabolicDynamicStatement.{u})
    (hG : IsConnectedReductive G) (f : ContinuousRationalFunctions F G)
    (hf : f ∈ normalizedParabolicCuspidalSubrepresentation F G hPD hG) :
    HasZeroProperParabolicConstantTerms (evaluate F G f) := by
  intro P U p r _ _ hp hr hpProper
  let := hG.isAffineHom
  let : IsClosedImmersion p.hom.hom.left := hp.isClosedSubgroup
  let : IsAffineHom P.X.hom := by rw [← Over.w p.hom.hom]; infer_instance
  let P' : ProperRationalParabolic G := ⟨⟨SubgroupFunctor.range p, ⟨P, p, hp, rfl⟩⟩, hpProper⟩
  have hEq : properRationalParabolicRadicals hPD hG P' = SubgroupFunctor.range (r ≫ p) :=
    properRationalParabolicRadicals_eq hPD hG hp hpProper hr.isGeometricUnipotentRadical.isUnipotentRadical
  funext g
  let avg (V : SubgroupFunctor G)
      (hV : IsClosed (AdelicSubgroupPoints.adelicPoints F G V : Set A)) : ℂ :=
    let : IsClosed (AdelicSubgroupPoints.adelicPoints F G V : Set A) := hV
    constantTerm F G V (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G V) f g
  have heqAvg {V W : SubgroupFunctor G} (h : V = W)
      (hV : IsClosed (AdelicSubgroupPoints.adelicPoints F G V : Set A))
      (hW : IsClosed (AdelicSubgroupPoints.adelicPoints F G W : Set A)) :
      avg V hV = avg W hW := by subst W; rfl
  rw [Pi.zero_apply, subgroupConstantTerm_eq_continuousConstantTerm (r ≫ p) f g]
  change avg (SubgroupFunctor.range (r ≫ p)) (AdelicSubgroupPoints.isClosed_adelicPoints_range F G (r ≫ p)) = 0
  rw [heqAvg hEq.symm _ (isClosed_properRationalParabolicRadicalAdelicPoints F G hPD hG P')]
  exact (mem_normalizedParabolicCuspidalSubrepresentation_iff F G hPD hG f).mp hf P' g

omit [LocallyOfFiniteType G.X.hom] in
private theorem directionalWords_leftInvariant {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    {f : A → ℂ} {r : A} (hf : ∀ x, f (r * x) = f x) (s : List (smoothModel F d)) :
    ∀ x, adelicIteratedDirectionalValue hsmooth s f (r * x) = adelicIteratedDirectionalValue hsmooth s f x := by
  induction s with
  | nil => exact hf
  | cons X s ih =>
    intro x
    simp only [adelicIteratedDirectionalValue_cons, adelicDirectionalValue, mul_assoc, ih]

variable (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]
  (hG : IsConnectedReductive G) {d N : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (rho : MatrixRepresentation G (Fin N))

local notation "Γ" => positiveRationalSubgroup F G T i
local notation "Q" => PositiveRationalQuotient F G T i
local notation "dq" => positiveRationalQuotientHaarMeasure F G T i
local notation "dg" => (Measure.haar : Measure A)
local notation "dΓ" => positiveRationalSubgroupHaarMeasure F G T i hi I e hc
local notation "V" => Lp ℂ 2 dq
local notation "H" => adelicHeight F G rho
local notation "smooth" => positiveQuotientLpSmoothing T i

include hi e hc hG in
/-- Rational height reduction upgrades the compact finite-slice estimates of
smoothed quotient classes to one exponent on the full adelic group. -/
theorem positiveQuotientLpSmoothing_globalGrowth (hN : 0 < N) (hrho : IsClosedSubgroup rho) :
    ∃ m : ℕ, ∀ (h : A → ℂ), IsAdelicTestFunction F G h →
      (∀ v : V, IsAdelicSmoothFunction F G (smooth h v)) ∧
      ∀ (s : List (smoothModel F d)), ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : V) (x : A),
        ‖adelicIteratedDirectionalValue hsmooth s (smooth h v) x‖ ≤ C * H x ^ m * ‖v‖ := by
  obtain ⟨K, D, m, hK, hD, hRed⟩ := adelicFullHeightRationalReduction rho hG hrho hN
  obtain ⟨b, hGrowth⟩ := groupSchemePositiveQuotientL2Smoothing T i hsmooth rho hi I e hc hN hrho
  refine ⟨m * b, fun h hh => ⟨(hGrowth h hh).1, ?_⟩⟩
  intro s
  obtain ⟨C, hC, hBound⟩ := (hGrowth h hh).2 s K hK
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  refine ⟨C * D ^ b, mul_nonneg hC (pow_nonneg hD₀ _), fun v x => ?_⟩
  obtain ⟨r, hrK, hrH⟩ := hRed x
  let r' : Γ := ⟨rational F G r, rationalSubgroup_le_positiveRationalSubgroup F G T i ⟨r, rfl⟩⟩
  rw [← directionalWords_leftInvariant hsmooth (positiveQuotientLpSmoothing_invariant T i h v r') s x]
  change ‖adelicIteratedDirectionalValue hsmooth s (smooth h v) (rational F G r * x)‖ ≤ _
  have hH₀ (y : A) : 0 ≤ H y := zero_le_one.trans (one_le_adelicHeight F G rho hN y)
  calc
    _ ≤ C * H (rational F G r * x) ^ b * ‖v‖ := hBound v _ hrK
    _ ≤ C * (D * H x ^ m) ^ b * ‖v‖ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hH₀ _) hrH b) hC) (norm_nonneg _)
    _ = _ := by rw [mul_pow, pow_mul]; ring

variable (hPD : ParabolicDynamicStatement.{u})

local notation "S" => fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
local notation "act" => fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc dg

/-- Smooth compact right convolutions act by Hilbert–Schmidt operators on
the full cuspidal Hilbert space of a connected reductive group. -/
def GroupSchemeCuspidalConvolutionCompactStatement : Prop :=
  0 < N → IsClosedSubgroup rho →
  ∀ (h : A → ℂ) (hhI : Integrable h dg), IsAdelicTestFunction F G h →
    IsHilbertSchmidt (act h hhI) ∧ IsCompactOperator (act h hhI)

theorem groupSchemeCuspidalConvolutionCompact :
    GroupSchemeCuspidalConvolutionCompactStatement T i hi I e hc hG rho hPD := by
  intro hN hrho h hhI hh
  let d := hG.smoothDimension
  have hsmooth : SmoothOfRelativeDimension d G.X.hom := hG.smoothDimension_spec
  let := positiveRationalQuotient_borelSpace F G T i hi I e hc
  let := positiveRationalQuotientHaarMeasure_isLocallyFiniteMeasure F G T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_isHaarMeasure F G T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_sigmaFinite F G T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_isMulRightInvariant F G T i hi I e hc
  let : IsFiniteMeasure dq := (positiveRationalQuotientHaarMeasure_isFiniteMeasure_iff F G T i hi I e hc).mpr
    (AdelicSiegelFactors.isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_connectedReductive F G hG)
  let kernel : C_c(A, ℂ) := ⟨⟨h, hh.1.1⟩, hh.2.1⟩
  obtain ⟨k, _, hk, _⟩ := Langlands.QuotientIntegration.quotientConvolutionKernel Γ
    (isClosed_positiveRationalSubgroup F G T i hi I e hc) dΓ dg dq
    (positiveRationalQuotientHaarMeasure_isCompatible F G T i hi I e hc) kernel
  let E := positiveQuotientHomeomorph F G T i hi I e hc
  let rep (q : Q) : normOneSubgroup F G := Quotient.out (E.symm q)
  have hRep (q : Q) : LeftCosetSpace.mk Γ (rep q).val = q := by
    rw [← positiveQuotientHomeomorph_mk F G T i hi I e hc]
    exact (congrArg E (Quotient.out_eq (E.symm q))).trans (E.apply_symm_apply q)
  let incl := (fullAEL2CuspidalInclusionLI F G hPD hG T i hi I e hc).toContinuousLinearMap
  let L (q : Q) : S →L[ℂ] ℂ := (innerSL ℂ (k (rep q).val)).comp incl
  have hL (v : S) (q : Q) : L q v = smooth h v.val (rep q).val := by
    change inner ℂ (k (rep q).val) v.val = smooth h v.val (rep q).val
    exact (hk _ v.val).2
  let B := incl.comp (act h hhI)
  have hB (v : S) : (B v : Q → ℂ) =ᵐ[dq] fun q => L q v := by
    change ((act h hhI v).val : Q → ℂ) =ᵐ[dq] _
    rw [fullAEL2CuspidalIntegratedAction_val]
    refine (positiveQuotientLpSmoothing_ae_eq T i hi I e hc h hhI v.val).trans
      (Filter.Eventually.of_forall fun q => ?_)
    calc
      _ = smooth h v.val (rep q).val := by nth_rw 1 [← hRep q]; rfl
      _ = L q v := (hL v q).symm
  obtain ⟨m, hGrowth⟩ := positiveQuotientLpSmoothing_globalGrowth T i hi I e hc hG hsmooth rho hN hrho
  obtain ⟨hSmooth, hGrowth⟩ := hGrowth h hh
  obtain ⟨C₀, _, hCover, hDecay⟩ := adelicNormOneCuspidalRapidDecay hsmooth rho hG hN
  have hEach (v : S) : ∃ C : ℝ, ∀ q : Q, ‖L q v‖ ≤ C := by
    let f := smooth h v.val
    have hInv' := positiveQuotientLpSmoothing_invariant T i h v.val
    have hInv : IsLeftInvariantUnder F G (rationalSubgroup F G) f := fun r hr x =>
      hInv' ⟨r, rationalSubgroup_le_positiveRationalSubgroup F G T i hr⟩ x
    let φ : C(Q, ℂ) := ⟨LeftCosetSpace.lift Γ f hInv',
      LeftCosetSpace.continuous_lift Γ _ _ (hSmooth v.val).1⟩
    have hφAE : ((act h hhI v).val : Q → ℂ) =ᵐ[dq] φ := by
      rw [fullAEL2CuspidalIntegratedAction_val]
      exact positiveQuotientLpSmoothing_ae_eq T i hi I e hc h hhI v.val
    have hφCus := (groupSchemeFullAEL2ContinuousCuspidality F G hPD hG T i hi I e hc
      φ (act h hhI v).val hφAE).mp (act h hhI v).2
    have hfCus : HasZeroProperParabolicConstantTerms f :=
      hasZeroProperParabolicConstantTerms_of_normalized hPD hG _ hφCus
    have hDer (s : List (smoothModel F d)) : ∃ C : ℝ, 0 ≤ C ∧
        ∀ x, ‖adelicIteratedDirectionalValue hsmooth s f x‖ ≤ C * H x ^ (m : ℝ) := by
      obtain ⟨C, hC, hC'⟩ := hGrowth s
      exact ⟨C * ‖v.val‖, mul_nonneg hC (norm_nonneg _), fun x => by
        rw [Real.rpow_natCast, mul_right_comm C]
        exact hC' v.val x⟩
    obtain ⟨C, _, hC⟩ := hDecay f (hSmooth v.val) hInv hfCus (m : ℝ) (Nat.cast_nonneg _) hDer 0
    refine ⟨C, fun q => ?_⟩
    obtain ⟨r, hr⟩ := hCover (rep q)
    rw [hL v q]
    change ‖f (rep q).val‖ ≤ C
    rw [← hInv _ ⟨r, rfl⟩]
    simpa only [pow_zero, mul_one] using hC _ hr
  obtain ⟨C, hC⟩ := banach_steinhaus (g := L) hEach
  have hHS := (hilbertSchmidtUniformEvaluation.{u, u, u} S Q dq B L (max 0 C) (le_max_left _ _)
    hB (Filter.Eventually.of_forall fun q => (hC q).trans (le_max_right _ _))).1
  have hHS' : IsHilbertSchmidt (act h hhI) := by
    obtain ⟨J, basis, hSummable⟩ := hHS
    refine ⟨J, basis, ?_⟩
    change Summable (fun t => ‖incl (act h hhI (basis t))‖ ^ 2) at hSummable
    have hNorm (v : S) : ‖incl v‖ = ‖v‖ :=
      (fullAEL2CuspidalInclusionLI F G hPD hG T i hi I e hc).norm_map v
    exact hSummable.congr fun t => congrArg (fun b : ℝ => b ^ 2) (hNorm (act h hhI (basis t)))
  exact ⟨hHS', hilbertSchmidtCompact S S _ hHS'⟩

end Langlands.Automorphic.GroupSchemeFunctions
