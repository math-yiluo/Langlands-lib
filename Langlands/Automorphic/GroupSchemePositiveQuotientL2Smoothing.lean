import Langlands.Automorphic.GroupSchemeQuotientL2Integrated
import Langlands.Analysis.Local.QuotientConvolutionKernelProof
import Langlands.Representation.Unitary.IntegratedTranslationPointwiseProof
import Langlands.Global.AdelicPositiveRationalConjugateGrowth
import Langlands.Global.AdelicRightConvolutionDifferentiation
import Langlands.Global.AdelicMaximalUnipotentDecay

/-! # Smooth representatives and growth of positive-quotient convolution -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Set
open scoped CategoryTheory.MonObj CompactlySupported Pointwise InnerProductSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus
  Langlands.Global.RepresentationGrowth Langlands.Global.InfiniteAdelicGroupPoints
  Langlands.GroupScheme Langlands.QuotientIntegration

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]

local notation "A" => AdelicGroupPoints F G
local notation "Γ" => positiveRationalSubgroup F G T i
local notation "Q" => PositiveRationalQuotient F G T i
local notation "dq" => positiveRationalQuotientHaarMeasure F G T i
local notation "dg" => (Measure.haar : Measure A)
local notation "dΓ" => positiveRationalSubgroupHaarMeasure F G T i hi I e hc
local notation "q" => LeftCosetSpace.mk Γ
local notation "V" => Lp ℂ 2 dq

/-- Compact right convolution of an `L²` class pulled back from the positive
rational quotient to the actual full group. -/
def positiveQuotientLpSmoothing (h : A → ℂ) (v : V) : A → ℂ :=
  rightConvolution F G h (v ∘ q)

private theorem exists_positiveQuotientKernel (h : C_c(A, ℂ)) :
    ∃ w : A → V, Continuous w ∧
      (∀ (x : A) (v : V), Integrable (fun a => h a * v (q (x * a))) dg ∧
        inner ℂ (w x) v = positiveQuotientLpSmoothing T i h v x) ∧
      ∀ (x : A) (M : ℝ), (∀ a, ‖h a‖ ≤ M) →
        ‖w x‖ ^ 2 ≤ M * (∫ a, ‖h a‖ ∂dg) *
          (dΓ).real (Subtype.val ⁻¹' ((fun s => x * s * x⁻¹) '' (tsupport h * (tsupport h)⁻¹))) := by
  let := positiveRationalQuotient_borelSpace F G T i hi I e hc
  let := positiveRationalQuotientHaarMeasure_isLocallyFiniteMeasure F G T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_isHaarMeasure F G T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_sigmaFinite F G T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_isMulRightInvariant F G T i hi I e hc
  exact quotientConvolutionKernel Γ (isClosed_positiveRationalSubgroup F G T i hi I e hc) dΓ dg dq
    (positiveRationalQuotientHaarMeasure_isCompatible F G T i hi I e hc) h

include hi e hc in
/-- The actual pullback of a quotient `L²` representative is integrable on
compact subsets of the adelic group. -/
theorem locallyIntegrable_positiveQuotientLpPullback (v : V) : LocallyIntegrable (v ∘ q) dg := by
  apply locallyIntegrable_iff.mpr
  intro S hS
  obtain ⟨b, hbS, _, hbComp, _⟩ := exists_continuous_one_zero_of_isCompact hS isClosed_empty (disjoint_empty S)
  let h : C_c(A, ℂ) := ⟨⟨fun x => (b x : ℂ), Complex.continuous_ofReal.comp b.continuous⟩,
    hbComp.comp_left Complex.ofReal_zero⟩
  obtain ⟨_, _, hIntegrable, _⟩ := exists_positiveQuotientKernel T i hi I e hc h
  apply ((hIntegrable 1 v).1).integrableOn.congr
  filter_upwards [ae_restrict_mem hS.isClosed.measurableSet] with x hx
  have hb : b x = 1 := hbS hx
  change (b x : ℂ) * v (q (1 * x)) = v (q x)
  simp only [hb, Complex.ofReal_one, one_mul]

omit [(characterRestrict i).range.FiniteIndex] [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant] in
/-- The pointwise smoothing is invariant on the actual positive rational quotient. -/
theorem positiveQuotientLpSmoothing_invariant (h : A → ℂ) (v : V) (r : Γ) (x : A) :
    positiveQuotientLpSmoothing T i h v (r.val * x) = positiveQuotientLpSmoothing T i h v x := by
  unfold positiveQuotientLpSmoothing rightConvolution
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun a => by
    simp only [Function.comp_apply, mul_assoc, LeftCosetSpace.mk_subgroup_mul]

/-- The quotient integral evaluated by the actual pointwise smoothing
represents the original integrated right action. -/
theorem positiveQuotientLpSmoothing_ae_eq (h : A → ℂ) (hh : Integrable h dg) (v : V) :
    (haarQuotientL2IntegratedAction F G T i hi I e hc dg h hh v : Q → ℂ) =ᵐ[dq]
      LeftCosetSpace.lift Γ (positiveQuotientLpSmoothing T i h v) (positiveQuotientLpSmoothing_invariant T i h v) := by
  let := positiveRationalQuotient_borelSpace F G T i hi I e hc
  let := positiveRationalQuotientHaarMeasure_isLocallyFiniteMeasure F G T i hi I e hc
  let : SecondCountableTopology Q :=
    TopologicalSpace.Quotient.secondCountableTopology (LeftCosetSpace.isOpenQuotientMap_mk Γ).isOpenMap
  let r := haarQuotientMeasureRightInvariant F G T i hi I e hc
  let act (x : Q) (a : A) := LeftCosetSpace.rightTranslate Γ a x
  have hAct : Continuous (fun z : Q × A => act z.1 z.2) :=
    continuous_smul.comp ((MulOpposite.continuous_op.comp continuous_snd).prodMk continuous_fst)
  have hp := Langlands.Analysis.integratedTranslationPointwise Q dq A dg act hAct.measurable r
    (haarQuotientL2BoundedRightAction F G T i hi I e hc)
    (norm_haarQuotientL2BoundedRightAction F G T i hi I e hc)
    (haarQuotientL2Orbit_aestronglyMeasurable F G T i hi I e hc dg)
    (fun a v => coeFn_quotientL2RightTranslate F G T i dq r a v) h hh v
  exact hp.2.trans (Filter.Eventually.of_forall fun z => by
    obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective Γ z
    rfl)

variable {d N : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom) (rho : MatrixRepresentation G (Fin N))

/-- Compact smooth kernels give smooth quotient representatives. One exponent
bounds every archimedean derivative on each compact finite slice, with a
constant proportional to the norm of the input class. -/
def GroupSchemePositiveQuotientL2SmoothingStatement : Prop :=
  ∀ (_hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
    (J : Type u) [Fintype J] (_e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) J)
    (_hc : IsCentral i) [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant],
  0 < N → IsClosedSubgroup rho → ∃ m : ℕ,
    ∀ (h : A → ℂ), IsAdelicTestFunction F G h →
      (∀ v : V, IsAdelicSmoothFunction F G (positiveQuotientLpSmoothing T i h v)) ∧
      ∀ (s : List (smoothModel F d)) (K : Set (FiniteAdelicGroupPoints F G)), IsCompact K →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : V) (x : A), finite F G x ∈ K →
          ‖adelicIteratedDirectionalValue hsmooth s (positiveQuotientLpSmoothing T i h v) x‖ ≤
            C * adelicHeight F G rho x ^ m * ‖v‖

omit [(characterRestrict i).range.FiniteIndex] [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant] in
theorem groupSchemePositiveQuotientL2Smoothing :
    GroupSchemePositiveQuotientL2SmoothingStatement T i hsmooth rho := by
  intro hi _ I _ e hc _ hN hrho
  let dH := positiveRationalSubgroupHaarMeasure F G T i hi I e hc
  let := positiveRationalQuotient_borelSpace F G T i hi I e hc
  obtain ⟨m, hMass⟩ := adelicPositiveRationalConjugateGrowth rho T i hi I e hc hN hrho
  have hMeas (v : V) : Measurable (v ∘ q) := (Lp.stronglyMeasurable v).measurable.comp
    (LeftCosetSpace.continuous_mk Γ).measurable
  have hLoc (v : V) := locallyIntegrable_positiveQuotientLpPullback T i hi I e hc v
  refine ⟨m, fun h hh => ⟨fun v => ?_, fun s K hK => ?_⟩⟩
  · exact (adelicRightConvolutionDifferentiation F G d hsmooth h _ hh (hMeas v) (hLoc v)).2.1
  let H := adelicHeight F G rho
  let k (s : List (smoothModel F d)) : A → ℂ :=
    s.foldr (rightConvolutionKernelDerivative hsmooth) h
  have hk (s : List (smoothModel F d)) : IsAdelicTestFunction F G (k s) := by
    induction s with
    | nil => exact hh
    | cons X s ih => exact (rightConvolutionKernelDerivative_isTestFunction hsmooth X ih).1
  have hDeriv (v : V) : ∀ s : List (smoothModel F d),
      adelicIteratedDirectionalValue hsmooth s (positiveQuotientLpSmoothing T i h v) =
        positiveQuotientLpSmoothing T i (k s) v := by
    intro s
    induction s with
    | nil => exact adelicIteratedDirectionalValue_nil hsmooth _
    | cons X s ih =>
      rw [adelicIteratedDirectionalValue_cons, ih]
      funext x
      rw [← pair_projections F G x, adelicDirectionalValue_pair]
      exact (adelicRightConvolutionDifferentiation F G d hsmooth (k s) _ (hk s) (hMeas v) (hLoc v)).2.2 X _ _
  let k₀ : C_c(A, ℂ) := ⟨⟨k s, (hk s).1.1⟩, (hk s).2.1⟩
  obtain ⟨w, _, hPair, hPairBound⟩ := exists_positiveQuotientKernel T i hi I e hc k₀
  obtain ⟨B, hB⟩ := k₀.hasCompactSupport.exists_bound_of_continuous k₀.continuous
  have hB₀ : 0 ≤ B := (norm_nonneg _).trans (hB 1)
  let L := B * ∫ a, ‖k₀ a‖ ∂dg
  have hL : 0 ≤ L := mul_nonneg hB₀ (integral_nonneg fun _ => norm_nonneg _)
  obtain ⟨C, hC, hBound⟩ := hMass K hK (tsupport k₀ * (tsupport k₀)⁻¹)
    (k₀.hasCompactSupport.mul k₀.hasCompactSupport.inv)
  refine ⟨Real.sqrt (L * C), Real.sqrt_nonneg _, fun v x hx => ?_⟩
  rw [hDeriv v s]
  change ‖positiveQuotientLpSmoothing T i (k₀ : A → ℂ) v x‖ ≤ _
  rw [← (hPair x v).2]
  have hHx : 1 ≤ H x := one_le_adelicHeight F G rho hN x
  have hHpow : 1 ≤ H x ^ m := one_le_pow₀ hHx
  apply (norm_inner_le_norm _ _).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (mul_nonneg hL hC), mul_assoc]
  calc
    ‖w x‖ ^ 2 ≤ L * dH.real (Subtype.val ⁻¹' ((fun t => x * t * x⁻¹) ''
        (tsupport k₀ * (tsupport k₀)⁻¹))) := hPairBound x B hB
    _ ≤ L * (C * H x ^ m) := mul_le_mul_of_nonneg_left (hBound x hx) hL
    _ ≤ L * (C * (H x ^ m) ^ 2) := by gcongr; exact le_self_pow₀ hHpow (by decide)

end Langlands.Automorphic.GroupSchemeFunctions
