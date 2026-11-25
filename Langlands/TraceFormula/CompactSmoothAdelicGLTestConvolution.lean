import Langlands.Global.AdelicGLTopology
import Langlands.Global.ArchimedeanGLDixmierMalliavin
import Langlands.Global.FiniteAdelicGroupCompactOpenBasisProof
import Langlands.Representation.Hecke.CommonInvarianceProof
import Langlands.TraceFormula.CompactSmoothAdelicGLTest

/-!
# Dixmier–Malliavin on tensor test functions of `GL_n(𝔸_E)`

`Langlands.TraceFormula.CompactSmoothAdelicGLTest.tensor_eq_sum_convolution`: for a smooth compactly
supported archimedean kernel `a` and a compactly supported locally constant `b` on `GL_n(𝔸_{E,f})`,
the tensor `a ⊗ b` is a finite sum `∑ᵢ (αᵢ ⊗ e) ⋆ (α'ᵢ ⊗ b)` of convolutions for a given left Haar
measure on `GL_n(𝔸_E)`, with the same finite component `b` on every right-hand factor. This is the
form a trace-formula consumer needs: conditions on `b` at a finite place pass to all right-hand
factors, and the finite component of each product is `e ⋆ b = b`.

`e` is the indicator of a compact open subgroup `K` of `GL_n(𝔸_f)` fixing `b` on the left
(`CompactFiniteGLTest.exists_compactOpen_leftInvariant`). For `y` with finite part in `K`,
`b(y_f⁻¹ g_f) = b(g_f)`, so the convolution reduces to an archimedean convolution for the measure
`finiteSliceMeasure μ K` (a left Haar measure on `GL_n(E_∞)`, `isHaarMeasure_finiteSliceMeasure`),
to which `ArchimedeanGL.SmoothCompactKernel.exists_eq_sum_convolution` applies. No comparison of
Haar measures of the factors is needed.
-/

noncomputable section

universe u

open MeasureTheory Set Filter Topology NumberField IsDedekindDomain
open scoped RestrictedProduct

namespace Langlands.TraceFormula

open Langlands.Global

variable (E : Type u) [Field E] [NumberField E] (n : ℕ)

/-- The finite adelic matrix group is Hausdorff. -/
theorem finiteAdelicGL_t2Space : T2Space (FiniteAdelicGL E n) := by
  let : T2Space (FiniteAdeleRing (𝓞 E) E) :=
    inferInstanceAs (T2Space (Πʳ v : HeightOneSpectrum (𝓞 E),
      [v.adicCompletion E, v.adicCompletionIntegers E]))
  let : T2Space (Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) :=
    inferInstanceAs (T2Space (Fin n → Fin n → FiniteAdeleRing (𝓞 E) E))
  infer_instance

/-- The finite adelic matrix group is totally disconnected (its matrix entries embed it in a product of
totally disconnected spaces). -/
theorem finiteAdelicGL_totallyDisconnectedSpace' :
    TotallyDisconnectedSpace (FiniteAdelicGL E n) := by
  let : TotallyDisconnectedSpace (FiniteAdeleRing (𝓞 E) E) :=
    finiteAdeles_totallyDisconnectedSpace E
  let : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → FiniteAdeleRing (𝓞 E) E))
  constructor
  exact isTotallyDisconnected_of_image Units.continuous_val.continuousOn Units.val_injective
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

/-- A compactly supported locally constant function on `GL_n(𝔸_f)` is left invariant under some compact
open subgroup (`Hecke.TestFunction.commonCompactOpenBiInvariance`). -/
theorem CompactFiniteGLTest.exists_compactOpen_leftInvariant (b : CompactFiniteGLTest E n) :
    ∃ K : OpenSubgroup (FiniteAdelicGL E n), IsCompact (K : Set (FiniteAdelicGL E n)) ∧
      ∀ k ∈ K, ∀ x, b.val (k * x) = b.val x := by
  have := finiteAdelicGL_t2Space E n
  have := finiteAdelicGL_totallyDisconnectedSpace' E n
  let b' : HarmonicAnalysis.SchwartzBruhat (FiniteAdelicGL E n) :=
    ⟨b.val, b.val.isLocallyConstant, b.property⟩
  obtain ⟨K, -, hKc, hK⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance
    (FiniteAdelicGL E n) {b'} ⊤
  exact ⟨K, hKc, fun k hk x => (hK b' (Finset.mem_singleton_self _)).1 ⟨k, hk⟩ x⟩

/-- The indicator function of a compact open subgroup, as a finite adelic test function. -/
def CompactFiniteGLTest.subgroupIndicator (K : OpenSubgroup (FiniteAdelicGL E n))
    (hK : IsCompact (K : Set (FiniteAdelicGL E n))) : CompactFiniteGLTest E n :=
  ⟨LocallyConstant.charFn ℂ K.isClopen, by
    rw [LocallyConstant.coe_charFn]
    exact HasCompactSupport.of_support_subset_isCompact hK support_indicator_subset⟩

/-- The values of a subgroup indicator. -/
theorem CompactFiniteGLTest.subgroupIndicator_apply (K : OpenSubgroup (FiniteAdelicGL E n))
    (hK : IsCompact (K : Set (FiniteAdelicGL E n))) (x : FiniteAdelicGL E n) :
    (subgroupIndicator E n K hK).val x =
      (K : Set (FiniteAdelicGL E n)).indicator (fun _ => (1 : ℂ)) x := by
  simp [subgroupIndicator, LocallyConstant.coe_charFn]
  rfl

section Measure

variable [MeasurableSpace (AdelicGL E n)] [BorelSpace (AdelicGL E n)]
  [MeasurableSpace (InfiniteAdelicGL E n)] [BorelSpace (InfiniteAdelicGL E n)]

/-- The measure `S ↦ μ({g : g_∞ ∈ S, g_f ∈ K})` on `GL_n(F_∞)`: the image under the infinite projection
of `μ` restricted to the elements with finite part in `K`. -/
def finiteSliceMeasure (μ : Measure (AdelicGL E n)) (K : Set (FiniteAdelicGL E n)) :
    Measure (InfiniteAdelicGL E n) :=
  (μ.restrict (AdelicGL.finite E n ⁻¹' K)).map (AdelicGL.infinite E n)

/-- For a left Haar measure `μ` on `GL_n(𝔸)` and a compact open subgroup `K` of `GL_n(𝔸_f)`,
`finiteSliceMeasure μ K` is a left Haar measure on `GL_n(F_∞)`. -/
theorem isHaarMeasure_finiteSliceMeasure (μ : Measure (AdelicGL E n)) [μ.IsHaarMeasure]
    (K : OpenSubgroup (FiniteAdelicGL E n)) (hK : IsCompact (K : Set (FiniteAdelicGL E n))) :
    (finiteSliceMeasure E n μ K).IsHaarMeasure := by
  set T : Set (AdelicGL E n) := AdelicGL.finite E n ⁻¹' (K : Set (FiniteAdelicGL E n))
  have hTo : IsOpen T := K.isOpen.preimage (AdelicGL.finite E n).continuous
  have hinf : Measurable (AdelicGL.infinite E n) := (AdelicGL.infinite E n).continuous.measurable
  have hset : ∀ C : Set (InfiniteAdelicGL E n),
      AdelicGL.infinite E n ⁻¹' C ∩ T = AdelicGL.split E n ⁻¹' (C ×ˢ (K : Set _)) := by
    intro C; ext y; rfl
  refine { toIsFiniteMeasureOnCompacts := ⟨fun C hC => ?_⟩,
           toIsMulLeftInvariant := ⟨fun c => ?_⟩,
           toIsOpenPosMeasure := ⟨fun O hO hne => ?_⟩ }
  · rw [finiteSliceMeasure, Measure.map_apply hinf hC.isClosed.measurableSet,
      Measure.restrict_apply' hTo.measurableSet, hset]
    exact ((AdelicGL.split E n).toHomeomorph.isCompact_preimage.2 (hC.prod hK)).measure_lt_top
  · have hc : Measurable (fun y : AdelicGL E n => AdelicGL.ofInfinite E n c * y) :=
      measurable_const_mul _
    have hT : (fun y : AdelicGL E n => AdelicGL.ofInfinite E n c * y) ⁻¹' T = T := by
      ext y
      change AdelicGL.finite E n (AdelicGL.ofInfinite E n c * y) ∈ (K : Set _) ↔
        AdelicGL.finite E n y ∈ (K : Set _)
      rw [map_mul]
      have : AdelicGL.finite E n (AdelicGL.ofInfinite E n c) = 1 := by
        change (AdelicGL.split E n (AdelicGL.ofInfinite E n c)).2 = 1
        change (AdelicGL.split E n ((AdelicGL.split E n).symm (c, 1))).2 = 1
        rw [ContinuousMulEquiv.apply_symm_apply]
      rw [this, one_mul]
    have hrestr : (μ.restrict T).map (fun y => AdelicGL.ofInfinite E n c * y) = μ.restrict T := by
      have h1 := (MeasurableEquiv.mulLeft (AdelicGL.ofInfinite E n c)).restrict_map μ T
      simp only [MeasurableEquiv.coe_mulLeft] at h1
      rw [hT] at h1
      rw [← h1, map_mul_left_eq_self]
    have hcomp : (fun z => c * z) ∘ (AdelicGL.infinite E n) =
        (AdelicGL.infinite E n) ∘ (fun y => AdelicGL.ofInfinite E n c * y) := by
      funext y
      have h1 : AdelicGL.infinite E n (AdelicGL.ofInfinite E n c) = c := by
        change (AdelicGL.split E n ((AdelicGL.split E n).symm (c, 1))).1 = c
        rw [ContinuousMulEquiv.apply_symm_apply]
      simp only [Function.comp_apply, map_mul, h1]
    rw [finiteSliceMeasure, Measure.map_map (measurable_const_mul c) hinf, hcomp,
      ← Measure.map_map hinf hc, hrestr]
  · rw [finiteSliceMeasure, Measure.map_apply hinf hO.measurableSet,
      Measure.restrict_apply' hTo.measurableSet]
    obtain ⟨o, ho⟩ := hne
    refine ((hO.preimage (AdelicGL.infinite E n).continuous).inter hTo).measure_ne_zero μ
      ⟨AdelicGL.pair E n o 1, ?_, ?_⟩
    · change AdelicGL.infinite E n (AdelicGL.pair E n o 1) ∈ O
      rwa [AdelicGL.infinite_pair]
    · change AdelicGL.finite E n (AdelicGL.pair E n o 1) ∈ (K : Set _)
      rw [AdelicGL.finite_pair]
      exact K.one_mem

end Measure

/-- The convolution `(α ⊗ 1_K) ⋆_μ (α' ⊗ b)`, for `b` left invariant under the compact open subgroup `K`,
is `b(g_f)` times the archimedean convolution `α ⋆ α'` at `g_∞` for the measure
`finiteSliceMeasure μ K`. -/
theorem CompactSmoothAdelicGLTest.convolution_tensor_subgroupIndicator
    [MeasurableSpace (AdelicGL E n)] [BorelSpace (AdelicGL E n)]
    [MeasurableSpace (InfiniteAdelicGL E n)] [BorelSpace (InfiniteAdelicGL E n)]
    (μ : Measure (AdelicGL E n)) (K : OpenSubgroup (FiniteAdelicGL E n))
    (hK : IsCompact (K : Set (FiniteAdelicGL E n))) (b : CompactFiniteGLTest E n)
    (hKb : ∀ k ∈ K, ∀ x, b.val (k * x) = b.val x)
    (α α' : ArchimedeanGL.SmoothCompactKernel E n) (g : AdelicGL E n) :
    ∫ y, adelicTestTensor E n α (CompactFiniteGLTest.subgroupIndicator E n K hK) y *
        adelicTestTensor E n α' b (y⁻¹ * g) ∂μ =
      (∫ z, α.val.val z * α'.val.val (z⁻¹ * AdelicGL.infinite E n g)
        ∂finiteSliceMeasure E n μ K) * b.val (AdelicGL.finite E n g) := by
  set T : Set (AdelicGL E n) := AdelicGL.finite E n ⁻¹' (K : Set (FiniteAdelicGL E n))
  have hTm : MeasurableSet T :=
    (K.isOpen.preimage (AdelicGL.finite E n).continuous).measurableSet
  have hinf : Measurable (AdelicGL.infinite E n) := (AdelicGL.infinite E n).continuous.measurable
  have hcont : Continuous fun z : InfiniteAdelicGL E n =>
      α.val.val z * α'.val.val (z⁻¹ * AdelicGL.infinite E n g) :=
    (ArchimedeanGL.continuous E n α.val).mul
      ((ArchimedeanGL.continuous E n α'.val).comp (continuous_inv.mul continuous_const))
  rw [finiteSliceMeasure, integral_map hinf.aemeasurable hcont.aestronglyMeasurable,
    ← integral_mul_const, ← integral_indicator hTm]
  congr 1
  funext y
  simp only [adelicTestTensor, ArchimedeanGL.kernelToContinuousMap_apply,
    CompactFiniteGLTest.subgroupIndicator_apply, map_mul, map_inv]
  by_cases hy : AdelicGL.finite E n y ∈ (K : Set (FiniteAdelicGL E n))
  · have hyT : y ∈ T := hy
    rw [indicator_of_mem hy, indicator_of_mem hyT, hKb _ (K.inv_mem hy)]
    ring
  · have hyT : y ∉ T := hy
    rw [indicator_of_notMem hy, indicator_of_notMem hyT]
    ring

/-- The factorization of `tensor_eq_sum_convolution` with the subgroup made explicit: there is a compact
open `K` fixing `b` on the left such that `a ⊗ b = ∑ᵢ (αᵢ ⊗ 1_K) ⋆_μ (α'ᵢ ⊗ b)`. -/
theorem CompactSmoothAdelicGLTest.exists_eq_sum_convolution_subgroupIndicator
    [MeasurableSpace (AdelicGL E n)] [BorelSpace (AdelicGL E n)]
    (μ : Measure (AdelicGL E n)) [μ.IsHaarMeasure]
    (a : ArchimedeanGL.SmoothCompactKernel E n) (b : CompactFiniteGLTest E n)
    {U : Set (InfiniteAdelicGL E n)} (hU : U ∈ 𝓝 1) :
    ∃ (K : OpenSubgroup (FiniteAdelicGL E n)) (hK : IsCompact (K : Set (FiniteAdelicGL E n))),
      (∀ k ∈ K, ∀ x, b.val (k * x) = b.val x) ∧
      ∃ (m : ℕ) (α α' : Fin m → ArchimedeanGL.SmoothCompactKernel E n),
        (∀ i, tsupport (α i).val.val ⊆ U ∧ tsupport (α' i).val.val ⊆ tsupport a.val.val) ∧
        ∀ g, adelicTestTensor E n a b g =
          ∑ i, ∫ y, adelicTestTensor E n (α i) (CompactFiniteGLTest.subgroupIndicator E n K hK) y *
            adelicTestTensor E n (α' i) b (y⁻¹ * g) ∂μ := by
  obtain ⟨K, hKc, hKb⟩ := CompactFiniteGLTest.exists_compactOpen_leftInvariant E n b
  let _ : MeasurableSpace (InfiniteAdelicGL E n) := ArchimedeanGL.borelMeasurableSpace E n
  have : BorelSpace (InfiniteAdelicGL E n) := ArchimedeanGL.borelMeasurableSpace_borelSpace E n
  have := isHaarMeasure_finiteSliceMeasure E n μ K hKc
  obtain ⟨m, α, α', hsupp, hsum⟩ :=
    ArchimedeanGL.SmoothCompactKernel.exists_eq_sum_convolution E n
      (finiteSliceMeasure E n μ K) hU a
  refine ⟨K, hKc, hKb, m, α, α', hsupp, fun g => ?_⟩
  rw [Finset.sum_congr rfl fun i _ =>
    CompactSmoothAdelicGLTest.convolution_tensor_subgroupIndicator E n μ K hKc b hKb (α i) (α' i) g,
    ← Finset.sum_mul, ← hsum]
  rfl

/-- **Dixmier–Malliavin on tensor tests of `GL_n(𝔸_E)`, keeping the finite component.** For a tensor
`a ⊗ b` (`adelicTestTensor`) and any left Haar measure `μ` on `GL_n(𝔸_E)`, there are smooth compactly
supported `αᵢ`, `α'ᵢ` on `GL_n(E_∞)` (with `αᵢ` supported in a prescribed neighbourhood of `1` and
`α'ᵢ` in the support of `a`) and a finite test `e` with
`a ⊗ b = ∑ᵢ (αᵢ ⊗ e) ⋆_μ (α'ᵢ ⊗ b)`: the right-hand factors keep `b`. Here `e = 1_K` for a compact
open subgroup `K` fixing `b` on the left, and the archimedean factorization is taken for the Haar
measure `finiteSliceMeasure μ K`. -/
theorem CompactSmoothAdelicGLTest.tensor_eq_sum_convolution
    [MeasurableSpace (AdelicGL E n)] [BorelSpace (AdelicGL E n)]
    (μ : Measure (AdelicGL E n)) [μ.IsHaarMeasure]
    (a : ArchimedeanGL.SmoothCompactKernel E n) (b : CompactFiniteGLTest E n)
    {U : Set (InfiniteAdelicGL E n)} (hU : U ∈ 𝓝 1) :
    ∃ (m : ℕ) (α α' : Fin m → ArchimedeanGL.SmoothCompactKernel E n)
      (e : CompactFiniteGLTest E n),
      (∀ i, tsupport (α i).val.val ⊆ U ∧ tsupport (α' i).val.val ⊆ tsupport a.val.val) ∧
      ∀ g, adelicTestTensor E n a b g =
        ∑ i, ∫ y, adelicTestTensor E n (α i) e y * adelicTestTensor E n (α' i) b (y⁻¹ * g) ∂μ := by
  obtain ⟨K, hK, -, m, α, α', hsupp, hsum⟩ :=
    CompactSmoothAdelicGLTest.exists_eq_sum_convolution_subgroupIndicator E n μ a b hU
  exact ⟨m, α, α', CompactFiniteGLTest.subgroupIndicator E n K hK, hsupp, hsum⟩

end Langlands.TraceFormula
