import Langlands.Global.AdelicParameterTwistAutomorphyReduction
import Langlands.Global.AdelicEisensteinConvolutionIdentity
import Langlands.Global.AdelicSmoothIwasawaHeight
import Langlands.Analysis.CompactManifoldIntegrableWeight

/-! # Smooth slices of induced convolution with a continuous compactly supported kernel -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Filter MeasureTheory NumberField Set Topology
open scoped CategoryTheory.MonObj ContDiff Manifold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicGroupPoints

open InfiniteAdelicGroupPoints Langlands.Analysis Langlands.Automorphic.GroupSchemeFunctions
  Langlands.GroupScheme

section RightConvolution

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)

local notation "H" => AdelicGroupPoints F G
local notation "Hinf" => InfiniteAdelicGroupPoints F G
local notation "Hfin" => FiniteAdelicGroupPoints F G
local notation "Iinf" => 𝓘(ℝ, smoothModel F d)
local notation "Icomplex" => 𝓘(ℝ, ℂ)
local notation "haar" => (Measure.haar : Measure H)

/-- A continuous compactly supported kernel convolves a continuous function to a continuous
function. -/
theorem continuous_rightConvolution_of_continuous {φ f : H → ℂ}
    (hφ : Continuous φ) (hsupp : HasCompactSupport φ) (hf : Continuous f) :
    Continuous (rightConvolution F G φ f) := by
  let integrand (g h : H) := φ h * f (g * h)
  have hcont : Continuous (Function.uncurry integrand) :=
    (hφ.comp continuous_snd).mul (hf.comp (continuous_fst.mul continuous_snd))
  have hmeas (g : H) : AEStronglyMeasurable (integrand g) haar :=
    (hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  apply continuous_iff_continuousAt.mpr
  intro g
  obtain ⟨D, hD, hDg⟩ := exists_compact_mem_nhds g
  obtain ⟨B, hB⟩ := (hD.prod hsupp).exists_bound_of_continuousOn hcont.continuousOn
  let majorant : H → ℝ := (tsupport φ).indicator fun _ => B
  have hmajorant : Integrable majorant haar :=
    (integrable_indicator_iff hsupp.isClosed.measurableSet).2
      (integrableOn_const (hsupp.measure_lt_top : haar (tsupport φ) < ⊤).ne)
  have hbd : ∀ᶠ y in 𝓝 g, ∀ᵐ x ∂haar, ‖integrand y x‖ ≤ majorant x := by
    filter_upwards [hDg] with y hy
    refine Eventually.of_forall fun x => ?_
    change ‖integrand y x‖ ≤ (tsupport φ).indicator (fun _ => B) x
    by_cases hx : x ∈ tsupport φ
    · rw [indicator_of_mem hx]
      exact hB (y, x) ⟨hy, hx⟩
    · simp [integrand, indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx]
  change ContinuousAt (fun y => ∫ x, integrand y x ∂haar) g
  apply continuousAt_of_dominated (Eventually.of_forall hmeas) hbd hmajorant
  exact Eventually.of_forall fun x =>
    (hcont.comp (continuous_id.prodMk continuous_const)).continuousAt

include hsmooth in
/-- Right convolution by a continuous compactly supported kernel preserves plot-smooth
infinite slices when the function being convolved is smooth with a fixed finite level. -/
theorem rightConvolution_plotSmoothSlice_of_smoothInput {φ f : H → ℂ}
    (hφ : Continuous φ) (hsupp : HasCompactSupport φ) (hf : IsAdelicSmoothFunction F G f)
    (b : Hfin) :
    functionInfiniteSlice F G (rightConvolution F G φ f) b ∈ InfinitePlotSmoothFunctions F G := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let : IsManifold Iinf ∞ Hinf := smoothIsManifold F G hsmooth
  let := smoothLieGroup F G hsmooth
  let (v : InfinitePlace F) : FiniteDimensional ℝ v.Completion := inferInstance
  obtain ⟨L, hL, hfix⟩ := hf.2.2
  let Q := Hfin ⧸ L
  let Z := Fin 0 → ℝ
  let : DiscreteTopology Q := QuotientGroup.discreteTopology hL
  let : ChartedSpace Z Q := ChartedSpace.ofDiscreteTopology
  let : IsManifold 𝓘(ℝ, Z) ∞ Q := IsManifold.of_discreteTopology ∞
  let : ChartedSpace (smoothModel F d × Z) (Hinf × Q) := prodChartedSpace _ _ _ _
  let : IsManifold 𝓘(ℝ, smoothModel F d × Z) ∞ (Hinf × Q) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod (I := Iinf) (I' := 𝓘(ℝ, Z)) Hinf Q
  let q : Hfin → Q := QuotientGroup.mk
  let kernel (z : Hinf × (Hinf × Q)) := f (pair F G (z.1 * z.2.1) (b * z.2.2.out))
  have hkernel : ContMDiff ((Iinf).prod 𝓘(ℝ, smoothModel F d × Z)) Icomplex ∞ kernel := by
    rw [modelWithCornersSelf_prod]
    intro z
    have hslice (c : Hfin) : ContMDiff Iinf Icomplex ∞ (fun a => f (pair F G a c)) :=
      (isPlotSmooth_iff_contMDiff F G hsmooth _).mp (hf.2.1 c)
    have hz := (hslice (b * z.2.2.out)).comp
      (contMDiff_fst.mul (contMDiff_fst.comp contMDiff_snd) :
        ContMDiff ((Iinf).prod ((Iinf).prod 𝓘(ℝ, Z))) Iinf ∞
          (fun w : Hinf × (Hinf × Q) => w.1 * w.2.1))
    apply (hz z).congr_of_eventuallyEq
    have hproj : Continuous (fun w : Hinf × (Hinf × Q) => w.2.2) :=
      continuous_snd.comp continuous_snd
    have hsingle : ({z.2.2} : Set Q) ∈ 𝓝 z.2.2 :=
      (isOpen_discrete _).mem_nhds (mem_singleton _)
    filter_upwards [(hproj.tendsto z).eventually hsingle] with w hw
    change w.2.2 = z.2.2 at hw
    change f (pair F G (w.1 * w.2.1) (b * w.2.2.out)) = _
    rw [hw]
    rfl
  let C := tsupport φ
  have hC : MeasurableSet C := hsupp.isClosed.measurableSet
  let : CompactSpace C := isCompact_iff_compactSpace.mp hsupp
  let measure : Measure C := (haar).comap Subtype.val
  let weight : C(C, ℂ) := ⟨fun h => φ h, hφ.comp continuous_subtype_val⟩
  let j : C(C, Hinf × Q) := ⟨fun h => (infinite F G h, q (finite F G h)),
    ((infinite F G).continuous.comp continuous_subtype_val).prodMk
      (QuotientGroup.continuous_mk.comp ((finite F G).continuous.comp continuous_subtype_val))⟩
  have hweight : Integrable weight measure :=
    (integrableOn_iff_comap_subtypeVal hC).mp (hφ.continuousOn.integrableOn_compact hsupp)
  obtain ⟨_, hsm, _⟩ := compactManifoldIntegrableWeight C (smoothModel F d) Hinf
    (smoothModel F d × Z) (Hinf × Q) ℂ measure weight weight.continuous.measurable hweight j
    kernel hkernel
  apply (isPlotSmooth_iff_contMDiff F G hsmooth _).mpr
  refine hsm.congr fun a => ?_
  have hker (x : C) : kernel (a, j x) = f (pair F G a b * x.val) := by
    obtain ⟨l, hl⟩ := QuotientGroup.mk_out_eq_mul (s := L) (finite F G x.val)
    change f (pair F G (a * infinite F G x.val) (b * (q (finite F G x.val)).out)) = _
    have hpair : pair F G a b * x.val =
        pair F G (a * infinite F G x.val) (b * finite F G x.val) := by
      rw [← pair_mul, pair_projections]
    rw [hl, hpair]
    simpa only [ofFinite_eq_pair, pair_mul, mul_one, mul_assoc] using
      hfix l.val l.property (pair F G (a * infinite F G x.val) (b * finite F G x.val))
  change (∫ x, φ x * f (pair F G a b * x) ∂haar) =
    ∫ x : C, weight x • kernel (a, j x) ∂measure
  simp_rw [hker]
  rw [show (∫ x : C, weight x • f (pair F G a b * x.val) ∂measure) =
      ∫ x in C, φ x * f (pair F G a b * x) ∂haar from
    integral_subtype_comap hC (fun x => φ x * f (pair F G a b * x))]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]).symm

end RightConvolution

section InducedConvolution

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)

omit [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
/-- The integrated induced action is ordinary convolution after twisting the input and
untwisting the output. -/
theorem IsIwasawaCompact.inducedConvolution_eq_heightPower_mul_rightConvolution
    (lam : ComplexCharacterParameter F P) (φ v : AdelicGroupPoints F G → ℂ)
    (g : AdelicGroupPoints F G) :
    hK.inducedConvolution lam φ v g =
      hK.heightPower (-lam) g * rightConvolution F G φ (hK.parameterTwist v lam) g := by
  simp only [IsIwasawaCompact.inducedConvolution, IsIwasawaCompact.inducedRightTranslate,
    rightConvolution, ← integral_const_mul]
  congr 1
  funext h
  rw [mul_left_comm]

/-- Compact support and continuity of the kernel and input give a continuous convolution
output for every parameter. -/
theorem IsIwasawaCompact.continuous_inducedConvolution (lam : ComplexCharacterParameter F P)
    {φ v : AdelicGroupPoints F G → ℂ} (hφ : Continuous φ) (hsupp : HasCompactSupport φ)
    (hv : Continuous v) : Continuous (hK.inducedConvolution lam φ v) := by
  rw [show hK.inducedConvolution lam φ v = fun g =>
      hK.heightPower (-lam) g * rightConvolution F G φ (hK.parameterTwist v lam) g from
    funext (hK.inducedConvolution_eq_heightPower_mul_rightConvolution lam φ v)]
  exact (hK.continuous_heightPower _).mul
    (continuous_rightConvolution_of_continuous hφ hsupp (hK.continuous_parameterTwist hv lam))

/-- For a maximal adelic Iwasawa compact, convolution of a smooth inducing function with a
continuous compactly supported kernel has plot-smooth infinite slices. -/
def InducedConvolutionSmoothSlicesStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left]
    (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
    {d : ℕ} (_hsmooth : SmoothOfRelativeDimension d G.X.hom), IsMaximalCompactSubgroup F G K →
    ∀ φ v : AdelicGroupPoints F G → ℂ, Continuous φ → HasCompactSupport φ →
      IsAdelicSmoothFunction F G v → ∀ (lam : ComplexCharacterParameter F P)
        (b : FiniteAdelicGroupPoints F G),
        functionInfiniteSlice F G (hK.inducedConvolution lam φ v) b ∈ InfinitePlotSmoothFunctions F G

/-- Differentiate the twisted inducing function through a compact integral in the
archimedean variables. -/
theorem inducedConvolutionSmoothSlices : InducedConvolutionSmoothSlicesStatement.{u} := by
  intro F _ _ G P _ _ _ p _ K hK d hsmooth hmax φ v hφ hsupp hv lam b
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  have hf := hK.isAdelicSmoothFunction_parameterTwist hmax hsmooth hv lam
  have hsm := rightConvolution_plotSmoothSlice_of_smoothInput hsmooth hφ hsupp hf b
  apply (isPlotSmooth_iff_contMDiff F G hsmooth _).mpr
  have hH := hK.hasSmoothHeightPairings_of_maximalCompact hsmooth hmax
  have hpow := (Complex.contDiff_exp (𝕜 := ℝ) (n := ∞)).contMDiff.comp (hH (-lam) b)
  have hmul : ContDiff ℝ ∞ (fun z : ℂ × ℂ => z.1 * z.2) := contDiff_mul
  have hp := hpow.prodMk_space ((isPlotSmooth_iff_contMDiff F G hsmooth _).mp hsm)
  refine (hmul.contMDiff.comp hp).congr fun a => ?_
  exact hK.inducedConvolution_eq_heightPower_mul_rightConvolution lam φ v (pair F G a b)

end InducedConvolution

end Langlands.Global.AdelicGroupPoints
