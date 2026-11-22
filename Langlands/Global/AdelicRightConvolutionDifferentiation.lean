import Langlands.Global.AdelicLocalFinitenessStatement
import Langlands.Analysis.CompactManifoldIntegrableWeight
import Langlands.Automorphic.GroupSchemeDifferential
import Langlands.Automorphic.GroupSchemeFiniteLevelSlices
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.MeasureTheory.Group.Integral

/-! # Smooth right convolution on actual adelic points -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory Filter MeasureTheory NumberField Set Topology
open scoped CategoryTheory.MonObj ContDiff Manifold Pointwise

namespace Langlands.Global.AdelicGroupPoints

open InfiniteAdelicGroupPoints Langlands.Analysis Langlands.Automorphic.GroupSchemeFunctions
  Langlands.Geometry.Manifold

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] {d : ℕ}
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)

local notation "A∞" => InfiniteAdelicGroupPoints F G
local notation "A_f" => FiniteAdelicGroupPoints F G
local notation "I∞" => 𝓘(ℝ, smoothModel F d)
local notation "Iℂ" => 𝓘(ℝ, ℂ)

/-- Differentiation of the test function by the inverse of the orbit parameter acting
on its left. This is the kernel derivative for positive right convolution. -/
def rightConvolutionKernelDerivative (X : smoothModel F d)
    (h : AdelicGroupPoints F G → ℂ) (a : AdelicGroupPoints F G) : ℂ := by
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  exact mvfderiv I∞ (fun t => h (ofInfinite F G t⁻¹ * a)) 1 X

private theorem mvfderiv_eq_of_eventuallyEq {f g : A∞ → ℂ} {a : A∞}
    (e : f =ᶠ[𝓝 a] g) :
    let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := smoothChartedSpace F G hsmooth
    mvfderiv I∞ f a = mvfderiv I∞ g a := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  change mvfderiv I∞ f a = mvfderiv I∞ g a
  unfold mvfderiv
  rw [e.mfderiv_eq]
  rfl

private theorem isAdelicSmoothFunction_of_slices {g : AdelicGroupPoints F G → ℂ}
    (L : Subgroup A_f) (hLo : IsOpen (L : Set A_f))
    (hL : ∀ l ∈ L, ∀ x, g (x * ofFinite F G l) = g x)
    (hs : let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      let := smoothChartedSpace F G hsmooth
      ∀ b : A_f, ContMDiff I∞ Iℂ ∞ (fun a => g (pair F G a b))) :
    IsAdelicSmoothFunction F G g := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  have hPlot (b : A_f) : functionInfiniteSlice F G g b ∈ InfinitePlotSmoothFunctions F G :=
    (isPlotSmooth_iff_contMDiff F G hsmooth _).mpr (hs b)
  let s (b : A_f) : InfinitePlotSmoothFunctions F G := ⟨functionInfiniteSlice F G g b, hPlot b⟩
  refine ⟨?_, hPlot, L, hLo, hL⟩
  have hcont := continuous_evaluatePlotSmoothSlices F G hsmooth s ⟨L, hLo⟩
    (fun b l => Subtype.ext (funext fun a => by
      change g (pair F G a (b * l.val)) = g (pair F G a b)
      simpa only [ofFinite_eq_pair, pair_mul, mul_one] using hL l l.property (pair F G a b)))
  exact hcont.congr fun x => congrArg g (pair_projections F G x)

/-- Differentiating a compact test kernel preserves both finite invariances and the support. -/
theorem rightConvolutionKernelDerivative_isTestFunction (X : smoothModel F d)
    {h : AdelicGroupPoints F G → ℂ} (hh : IsAdelicTestFunction F G h) :
    IsAdelicTestFunction F G (rightConvolutionKernelDerivative hsmooth X h) ∧
      tsupport (rightConvolutionKernelDerivative hsmooth X h) ⊆ tsupport h := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let k := rightConvolutionKernelDerivative hsmooth X h
  have hsupp : tsupport k ⊆ tsupport h := by
    apply closure_minimal _ (isClosed_tsupport h)
    intro x hx
    by_contra hx'
    have hc : Continuous (fun t : A∞ => ofInfinite F G t⁻¹ * x) :=
      ((ofInfinite F G).continuous.comp continuous_inv).mul continuous_const
    have he : (fun t : A∞ => h (ofInfinite F G t⁻¹ * x)) =ᶠ[𝓝 1] fun _ => 0 := by
      have hu : (tsupport h)ᶜ ∈ 𝓝 (ofInfinite F G (1 : A∞)⁻¹ * x) :=
        (isClosed_tsupport h).isOpen_compl.mem_nhds
          (by simpa only [mem_compl_iff, inv_one, map_one, one_mul] using hx')
      exact ((hc.tendsto 1).eventually hu).mono fun _ ht => image_eq_zero_of_notMem_tsupport ht
    apply hx
    change mvfderiv I∞ _ 1 X = 0
    rw [mvfderiv_eq_of_eventuallyEq hsmooth he, mvfderiv_const, zero_apply]
  obtain ⟨L, hLo, hL⟩ := hh.1.2.2
  obtain ⟨U, hUo, hU⟩ := hh.2.2
  have hkr (l : A_f) (hl : l ∈ L) (x : AdelicGroupPoints F G) :
      k (x * ofFinite F G l) = k x := by
    unfold k rightConvolutionKernelDerivative
    apply congrArg (fun k : A∞ → ℂ => mvfderiv I∞ k 1 X)
    funext t
    rw [← mul_assoc, hL l hl]
  have hkl (l : A_f) (hl : l ∈ U) (x : AdelicGroupPoints F G) :
      k (ofFinite F G l * x) = k x := by
    unfold k rightConvolutionKernelDerivative
    apply congrArg (fun k : A∞ → ℂ => mvfderiv I∞ k 1 X)
    funext t
    rw [← mul_assoc, (factors_commute F G t⁻¹ l).eq, mul_assoc, hU l hl]
  refine ⟨⟨isAdelicSmoothFunction_of_slices hsmooth L hLo hkr ?_,
    hh.2.1.of_isClosed_subset (isClosed_tsupport k) hsupp, U, hUo, hkl⟩, hsupp⟩
  change ∀ b : A_f, ContMDiff I∞ Iℂ ∞ (fun a => k (pair F G a b))
  intro b
  have hb : ContMDiff I∞ Iℂ ∞ (fun a => h (pair F G a b)) :=
    (isPlotSmooth_iff_contMDiff F G hsmooth _).mp (hh.1.2.1 b)
  have hbi : ContMDiff I∞ Iℂ ∞ (fun a : A∞ => h (pair F G a⁻¹ b)) :=
    hb.comp (contMDiff_inv I∞ ∞)
  apply ((contMDiff_groupDirectionalValue I∞ X hbi).comp (contMDiff_inv I∞ ∞)).congr
  intro a
  change k (pair F G a b) = groupDirectionalValue I∞ X (fun y => h (pair F G y⁻¹ b)) a⁻¹
  unfold k rightConvolutionKernelDerivative groupDirectionalValue
  apply congrArg (fun k : A∞ → ℂ => mvfderiv I∞ k 1 X)
  funext t
  dsimp only
  rw [ofInfinite_eq_pair, pair_mul, one_mul, mul_inv_rev, inv_inv]

variable [LocallyOfFiniteType G.X.hom]

local notation "μG" => (Measure.haar : Measure (AdelicGroupPoints F G))

/-- Left Haar change of variable writes the convolution with the inverse output
point in the kernel argument. -/
theorem rightConvolution_eq_integral_leftKernel (h f : AdelicGroupPoints F G → ℂ)
    (x : AdelicGroupPoints F G) :
    rightConvolution F G h f x = ∫ z, f z * h (x⁻¹ * z) ∂μG := by
  simpa only [rightConvolution, inv_mul_cancel_left, mul_comm] using
    integral_mul_left_eq_self («μ» := μG) (fun z => f z * h (x⁻¹ * z)) x

private theorem rightConvolution_integrable {h f : AdelicGroupPoints F G → ℂ}
    (hh : Continuous h) (hc : HasCompactSupport h) (hf : LocallyIntegrable f μG)
    (x : AdelicGroupPoints F G) : Integrable (fun a => h a * f (x * a)) μG := by
  let h' (z : AdelicGroupPoints F G) := h (x⁻¹ * z)
  have hh' : Continuous h' := hh.comp (continuous_const.mul continuous_id)
  have hc' : HasCompactSupport h' := hc.comp_homeomorph (Homeomorph.mulLeft x⁻¹)
  obtain ⟨B, hB⟩ := hc'.exists_bound_of_continuous hh'
  have hs : Function.support (fun z => f z • h' z) ⊆ tsupport h' := by
    intro z hz
    by_contra hnot
    apply hz
    change f z • h' z = 0
    rw [image_eq_zero_of_notMem_tsupport hnot, smul_zero]
  have hi : Integrable (fun z => f z • h' z) μG :=
    (integrableOn_iff_integrable_of_support_subset hs).mp
      ((hf.integrableOn_isCompact hc').smul_bdd B hh'.aestronglyMeasurable
        (Filter.Eventually.of_forall hB))
  simpa only [Function.comp_def, h', inv_mul_cancel_left, smul_eq_mul, mul_comm] using
    (measurePreserving_mul_left μG x).integrable_comp_of_integrable hi

private theorem rightConvolution_finite_level {h f : AdelicGroupPoints F G → ℂ}
    (L : Subgroup A_f) (hL : ∀ l ∈ L, ∀ x, h (ofFinite F G l * x) = h x)
    (l : A_f) (hl : l ∈ L) (x : AdelicGroupPoints F G) :
    rightConvolution F G h f (x * ofFinite F G l) = rightConvolution F G h f x := by
  rw [rightConvolution_eq_integral_leftKernel, rightConvolution_eq_integral_leftKernel]
  simp only [mul_inv_rev, ← map_inv, mul_assoc, hL _ (L.inv_mem hl)]

private theorem rightConvolution_slice_at {h f : AdelicGroupPoints F G → ℂ}
    (hh : IsAdelicTestFunction F G h) (hf : Measurable f) (hfi : LocallyIntegrable f μG)
    (a : A∞) (b : A_f) :
    let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := smoothChartedSpace F G hsmooth
    ContMDiffAt I∞ Iℂ ∞ (fun y => rightConvolution F G h f (pair F G y b)) a ∧
    ∀ X : smoothModel F d,
      groupDirectionalValue I∞ X (fun y => rightConvolution F G h f (pair F G y b)) a =
        rightConvolution F G (rightConvolutionKernelDerivative hsmooth X h) f (pair F G a b) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let : IsManifold I∞ ∞ A∞ := smoothIsManifold F G hsmooth
  let := smoothLieGroup F G hsmooth
  let (v : InfinitePlace F) : FiniteDimensional ℝ v.Completion := inferInstance
  obtain ⟨L, hLo, hL⟩ := hh.2.2
  let Q := A_f ⧸ L
  let Z := Fin 0 → ℝ
  let : DiscreteTopology Q := QuotientGroup.discreteTopology hLo
  let : ChartedSpace Z Q := ChartedSpace.ofDiscreteTopology
  let : IsManifold 𝓘(ℝ, Z) ∞ Q := IsManifold.of_discreteTopology ∞
  let : ChartedSpace (smoothModel F d × Z) (A∞ × Q) := prodChartedSpace _ _ _ _
  let : IsManifold 𝓘(ℝ, smoothModel F d × Z) ∞ (A∞ × Q) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod (I := I∞) (I' := 𝓘(ℝ, Z)) A∞ Q
  let q : A_f → Q := QuotientGroup.mk
  let k (p : A∞ × (A∞ × Q)) : ℂ :=
    h (pair F G (p.1⁻¹ * p.2.1) p.2.2.out⁻¹)
  have hk : ContMDiff (I∞.prod 𝓘(ℝ, smoothModel F d × Z)) Iℂ ∞ k := by
    rw [modelWithCornersSelf_prod]
    intro p
    have hb (c : A_f) : ContMDiff I∞ Iℂ ∞ (fun y => h (pair F G y c)) :=
      (isPlotSmooth_iff_contMDiff F G hsmooth _).mp (hh.1.2.1 c)
    have hk' := (hb p.2.2.out⁻¹).comp
      (contMDiff_fst.inv.mul (contMDiff_fst.comp contMDiff_snd) :
        ContMDiff (I∞.prod (I∞.prod 𝓘(ℝ, Z))) I∞ ∞
          (fun r : A∞ × (A∞ × Q) => r.1⁻¹ * r.2.1))
    apply (hk' p).congr_of_eventuallyEq
    have hc : Continuous (fun r : A∞ × (A∞ × Q) => r.2.2) :=
      continuous_snd.comp continuous_snd
    have he : ({p.2.2} : Set Q) ∈ 𝓝 p.2.2 :=
      (_root_.isOpen_discrete _).mem_nhds (mem_singleton _)
    filter_upwards [(hc.tendsto p).eventually he] with r hr
    change r.2.2 = p.2.2 at hr
    change h (pair F G (r.1⁻¹ * r.2.1) r.2.2.out⁻¹) = _
    rw [hr]
    rfl
  obtain ⟨D, hDc, hD⟩ := exists_compact_mem_nhds a
  let embed (y : A∞) := pair F G y b
  have hpair : Continuous (fun y : A∞ => (y, b)) := Continuous.prodMk_left b
  have hembed : Continuous embed := by
    change Continuous ((fun z : A∞ × A_f => pair F G z.1 z.2) ∘ fun y : A∞ => (y, b))
    exact (continuous_pair F G).comp hpair
  let C : Set (AdelicGroupPoints F G) := (embed '' D) * tsupport h
  have hC : IsCompact C := (hDc.image hembed).mul hh.2.1
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let νC : Measure C := (μG).comap Subtype.val
  let fC (z : C) := f z.val
  have hfC : Measurable fC := hf.comp measurable_subtype_coe
  have hfiC : Integrable fC νC :=
    (integrableOn_iff_comap_subtypeVal hCm).mp (hfi.integrableOn_isCompact hC)
  let j : C(C, A∞ × Q) := ⟨fun z => (infinite F G z, q ((finite F G z)⁻¹ * b)),
    ((infinite F G).continuous.comp continuous_subtype_val).prodMk
      (QuotientGroup.continuous_mk.comp
        (((finite F G).continuous.comp continuous_subtype_val).inv.mul continuous_const))⟩
  have hker (y : A∞) (z : C) : k (y, j z) = h ((embed y)⁻¹ * z.val) := by
    obtain ⟨l, hl⟩ := QuotientGroup.mk_out_eq_mul (s := L) ((finite F G z)⁻¹ * b)
    change h (pair F G (y⁻¹ * infinite F G z) (q ((finite F G z)⁻¹ * b)).out⁻¹) = _
    have hq : (q ((finite F G z)⁻¹ * b)).out = (finite F G z)⁻¹ * b * l := hl
    have hinv : (embed y)⁻¹ * z.val =
        pair F G (y⁻¹ * infinite F G z) (b⁻¹ * finite F G z) := by
      apply (split F G).injective
      simp only [split_apply, map_mul, map_inv, embed, infinite_pair, finite_pair]
      rfl
    rw [hq, hinv, mul_inv_rev, mul_inv_rev, inv_inv]
    simpa only [ofFinite_eq_pair, pair_mul, one_mul] using
      hL l.val⁻¹ (L.inv_mem l.property) (pair F G (y⁻¹ * infinite F G z) (b⁻¹ * finite F G z))
  have hzero (y : A∞) (hy : y ∈ D) (z : AdelicGroupPoints F G) (hz : z ∉ C) :
      (embed y)⁻¹ * z ∉ tsupport h := by
    intro hmem
    apply hz
    exact ⟨embed y, mem_image_of_mem embed hy, (embed y)⁻¹ * z, hmem, mul_inv_cancel_left _ _⟩
  have heval (y : A∞) (hy : y ∈ D) :
      rightConvolution F G h f (embed y) = ∫ z, fC z • k (y, j z) ∂νC := by
    rw [rightConvolution_eq_integral_leftKernel]
    simp_rw [hker]
    rw [show (∫ z : C, fC z • h ((embed y)⁻¹ * z.val) ∂νC) =
        ∫ z in C, f z * h ((embed y)⁻¹ * z) ∂μG from
      integral_subtype_comap hCm (fun z => f z * h ((embed y)⁻¹ * z))]
    symm
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
      rw [image_eq_zero_of_notMem_tsupport (hzero y hy z hz), mul_zero]
  obtain ⟨_, hsm, _⟩ := compactManifoldIntegrableWeight C (smoothModel F d) A∞
    (smoothModel F d × Z) (A∞ × Q) ℂ νC fC hfC hfiC j k hk
  refine ⟨(hsm a).congr_of_eventuallyEq
    ((show ∀ᶠ y in 𝓝 a, y ∈ D from hD).mono heval), fun X => ?_⟩
  let ka (p : A∞ × (A∞ × Q)) := k (a * p.1, p.2)
  have hka : ContMDiff (I∞.prod 𝓘(ℝ, smoothModel F d × Z)) Iℂ ∞ ka :=
    hk.comp ((contMDiff_const.mul contMDiff_fst).prodMk contMDiff_snd)
  obtain ⟨_, _, hderiv⟩ := compactManifoldIntegrableWeight C (smoothModel F d) A∞
    (smoothModel F d × Z) (A∞ × Q) ℂ νC fC hfC hfiC j ka hka
  have heq : (fun t : A∞ => rightConvolution F G h f (embed (a * t))) =ᶠ[𝓝 1]
      (fun t : A∞ => ∫ z, fC z • ka (t, j z) ∂νC) := by
    have ha : Continuous (fun t : A∞ => a * t) := continuous_const.mul continuous_id
    have he : ∀ᶠ y in 𝓝 (a * (1 : A∞)), y ∈ D := by rw [mul_one]; exact hD
    exact ((ha.tendsto 1).eventually he).mono
      (fun t ht => heval (a * t) ht)
  change mvfderiv I∞ _ 1 X = _
  rw [mvfderiv_eq_of_eventuallyEq hsmooth heq, hderiv, rightConvolution_eq_integral_leftKernel]
  have hkderiv (z : C) : mvfderiv I∞ (fun t => ka (t, j z)) 1 X =
      rightConvolutionKernelDerivative hsmooth X h ((embed a)⁻¹ * z.val) := by
    unfold rightConvolutionKernelDerivative
    apply congrArg (fun k : A∞ → ℂ => mvfderiv I∞ k 1 X)
    funext t
    change k (a * t, j z) = _
    rw [hker]
    congr 1
    have ht : embed (a * t) = embed a * ofInfinite F G t := by
      simp only [embed, ofInfinite_eq_pair, pair_mul, mul_one]
    rw [ht, mul_inv_rev, map_inv, mul_assoc]
  simp_rw [hkderiv]
  rw [show (∫ z : C, fC z • rightConvolutionKernelDerivative hsmooth X h
      ((embed a)⁻¹ * z.val) ∂νC) =
      ∫ z in C, f z * rightConvolutionKernelDerivative hsmooth X h ((embed a)⁻¹ * z) ∂μG from
    integral_subtype_comap hCm (fun z => f z *
      rightConvolutionKernelDerivative hsmooth X h ((embed a)⁻¹ * z))]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  have hn := hzero a (mem_of_mem_nhds hD) z hz
  rw [image_eq_zero_of_notMem_tsupport (fun hmem => hn
    ((rightConvolutionKernelDerivative_isTestFunction hsmooth X hh).2 hmem)), mul_zero]

/-- A compact smooth test kernel smooths a locally integrable input on the actual adelic group.
Its first archimedean derivatives are obtained by differentiating the kernel. -/
def AdelicRightConvolutionDifferentiationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (d : ℕ) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (h f : AdelicGroupPoints F G → ℂ),
    IsAdelicTestFunction F G h → Measurable f →
    LocallyIntegrable f (Measure.haar : Measure (AdelicGroupPoints F G)) →
    (∀ x, Integrable (fun a => h a * f (x * a)) Measure.haar) ∧
    IsAdelicSmoothFunction F G (rightConvolution F G h f) ∧
    (let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
     let := smoothChartedSpace F G hsmooth
     ∀ (X : smoothModel F d) (a : InfiniteAdelicGroupPoints F G) (b : FiniteAdelicGroupPoints F G),
       groupDirectionalValue 𝓘(ℝ, smoothModel F d) X
         (fun y => rightConvolution F G h f (pair F G y b)) a =
         rightConvolution F G (rightConvolutionKernelDerivative hsmooth X h) f (pair F G a b))

theorem adelicRightConvolutionDifferentiation : AdelicRightConvolutionDifferentiationStatement.{u} := by
  intro F _ _ G _ _ d hsmooth h f hh hf hfi
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  obtain ⟨L, hLo, hL⟩ := hh.2.2
  refine ⟨rightConvolution_integrable hh.1.1 hh.2.1 hfi,
    isAdelicSmoothFunction_of_slices hsmooth L hLo (rightConvolution_finite_level L hL) ?_, ?_⟩
  · exact fun b a => (rightConvolution_slice_at hsmooth hh hf hfi a b).1
  · exact fun X a b => (rightConvolution_slice_at hsmooth hh hf hfi a b).2 X

end Langlands.Global.AdelicGroupPoints
