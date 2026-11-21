import Langlands.Representation.Archimedean.RealCartanTraceCoordinates
import Mathlib.Topology.UrysohnsLemma

/-! # Localization of the weighted compact Cartan trace -/

noncomputable section

open Matrix MeasureTheory Set Filter Metric
open scoped Matrix.Norms.Operator Topology ENNReal

namespace Langlands.Archimedean.RealCartanTraceLocalization

open RealCartanAngularFrame RealCartanCompactSupport RealCartanLowerCoordinates RealCartanTraceCoordinates
  RealLeviChart RealLeviCompactChart RealPrincipalSeriesDuality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local notation "Ortho" n:max => Matrix.unitaryGroup (Fin n) ℝ

attribute [local instance] measurableSpaceK RealLeviBlockHaar.secondCountableTopology_GL
  RealLeviBlockHaar.secondCountableTopology_O
local instance borelSpaceK (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

private theorem eventually_vanish_on {α K : Type*} [TopologicalSpace α] [TopologicalSpace K]
    [T2Space K] [One K] {B : Set α} {A : α → K} (hB : IsCompact B) (hA : Continuous A)
    (hfix : ∀ b ∈ B, A b ≠ 1) (φ : ℝ → C(K, ℂ))
    (hφ : ∀ U : Set K, IsOpen U → 1 ∈ U →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), Function.support (φ ε) ⊆ U) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ b ∈ B, φ ε (A b) = 0 := by
  let U := (A '' B)ᶜ
  have hU : IsOpen U := (hB.image hA).isClosed.isOpen_compl
  have h1 : 1 ∈ U := by
    rintro ⟨b, hb, he⟩
    exact hfix b hb he
  filter_upwards [hφ U hU h1] with ε hε b hb
  by_contra hne
  exact hε hne ⟨b, hb, rfl⟩

private theorem exists_cutoff {K : Type*} [TopologicalSpace K] [NormalSpace K] {S U : Set K}
    (hS : IsClosed S) (hU : IsOpen U) (hSU : S ⊆ U) :
    ∃ V : Set K, IsOpen V ∧ S ⊆ V ∧ ∃ η : C(K, ℂ), EqOn η 1 V ∧ tsupport η ⊆ U := by
  obtain ⟨W, hW, hSW, hWU⟩ := normal_exists_closure_subset hS hU hSU
  obtain ⟨V, hV, hSV, hVW⟩ := normal_exists_closure_subset hS hW hSW
  have hdisj : Disjoint Wᶜ (closure V) := Set.disjoint_left.mpr fun _ h₁ h₂ => h₁ (hVW h₂)
  obtain ⟨f, hf₀, hf₁, _⟩ := exists_continuous_zero_one_of_isClosed hW.isClosed_compl
    isClosed_closure hdisj
  let η : C(K, ℂ) := ⟨fun y => (f y : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  refine ⟨V, hV, hSV, η, fun y hy => ?_, (closure_mono ?_).trans hWU⟩
  · change (f y : ℂ) = 1
    rw [hf₁ (subset_closure hy), Pi.one_apply, Complex.ofReal_one]
  · intro y hy
    by_contra h
    exact hy (by change (f y : ℂ) = 0; rw [hf₀ h, Pi.zero_apply, Complex.ofReal_zero])

section Setup

variable {c : ℕ} (sz : Fin c → ℕ)

local notation "N" => ∑ i, sz i
local notation "K" => Ortho N
local notation "G" => Langlands.GeneralLinear N ℝ
local notation "H" => LeviFrame sz
local notation "XSpace" => (Coord sz → ℝ)
local notation "ZSpace" => (WithinIndex sz → ℝ)
local notation "E" => (XSpace × ZSpace)

/-- The weighted compact trace integral before imposing the surviving filter. -/
def weightedIntegral (g : G) (W : C(K × H, ℂ)) (φ : C(K, ℂ)) : ℂ :=
  ∫ y, ∫ h, W (y, h) * φ (compactArgument g y (blockFrame sz h)) ∂frameMeasure sz ∂compactHaar N

private def testArgument (g : G) (p : K × H) : K :=
  compactArgument g p.1 (blockFrame sz p.2)

private theorem continuous_testArgument (g : G) : Continuous (testArgument sz g) := by
  have hfst : Continuous (Prod.fst : K × H → K) := continuous_fst
  have hsnd : Continuous (Prod.snd : K × H → H) := continuous_snd
  have hh := (continuous_blockFrame sz).comp hsnd
  unfold testArgument
  simpa only [Function.comp_def] using (continuous_compactArgument g).comp (hfst.prodMk hh)

private def patchWeight (η : C(K, ℂ)) (W : C(K × H, ℂ)) : C(K × H, ℂ) :=
  ⟨fun p => η p.1 * W p, (η.continuous.comp continuous_fst).mul W.continuous⟩

private def patchIntegrand (g : G) (η : C(K, ℂ)) (W : C(K × H, ℂ)) (φ : C(K, ℂ))
    (p : K × H) : ℂ := patchWeight sz η W p * φ (testArgument sz g p)

private theorem continuous_patchIntegrand (g : G) (η : C(K, ℂ)) (W : C(K × H, ℂ))
    (φ : C(K, ℂ)) : Continuous (patchIntegrand sz g η W φ) :=
  (patchWeight sz η W).continuous.mul (φ.continuous.comp (continuous_testArgument sz g))

private theorem continuous_inner (F : C(K × H, ℂ)) :
    Continuous (fun y => ∫ h, F (y, h) ∂frameMeasure sz) := by
  have hc := continuous_parametric_integral_of_continuous (μ := frameMeasure sz)
    (f := fun y h => F (y, h)) F.continuous (isCompact_univ (X := H))
  simpa only [Measure.restrict_univ] using hc

variable {ι : Type*} [Fintype ι]

private def fixedSet (w : ι → K) (i : ι) : Set K := range (fun κ => blockFrame sz κ * w i)

omit [Fintype ι] in
private theorem isCompact_fixedSet (w : ι → K) (i : ι) : IsCompact (fixedSet sz w i) :=
  isCompact_range ((continuous_blockFrame sz).mul continuous_const)

private theorem exists_coset_cutoffs (w : ι → K)
    (hdisj : Pairwise (fun i j => Disjoint (fixedSet sz w i) (fixedSet sz w j))) :
    ∃ V : ι → Set K, (∀ i, IsOpen (V i)) ∧ (∀ i, fixedSet sz w i ⊆ V i) ∧
      ∃ η : ι → C(K, ℂ), (∀ i, EqOn (η i) 1 (V i)) ∧
        (∀ i j, i ≠ j → Disjoint (tsupport (η i)) (fixedSet sz w j)) ∧
        ∀ i κ X, placedFrame sz (w i) κ X ∈ tsupport (η i) → ‖X‖ < 1 := by
  obtain ⟨U, hU, hU₁, hUX⟩ := realLeviCompactChartSupport c sz 1 zero_lt_one
  let other (i : ι) : Set K := ⋃ j : {j : ι // j ≠ i}, fixedSet sz w j
  have hother (i : ι) : IsClosed (other i) :=
    isClosed_iUnion_of_finite fun j => (isCompact_fixedSet sz w j).isClosed
  let O (i : ι) := (fun y : K => y * (w i)⁻¹) ⁻¹' U ∩ (other i)ᶜ
  have hO (i : ι) : IsOpen (O i) :=
    (hU.preimage (continuous_id.mul continuous_const)).inter (hother i).isOpen_compl
  have hsub (i : ι) : fixedSet sz w i ⊆ O i := by
    rintro y ⟨κ, rfl⟩
    refine ⟨?_, ?_⟩
    · change blockFrame sz κ * w i * (w i)⁻¹ ∈ U
      rw [mul_inv_cancel_right]
      exact hU₁ (mem_range_self κ)
    · intro h
      obtain ⟨j, hj⟩ := mem_iUnion.mp h
      exact (Set.disjoint_left.mp (hdisj j.2.symm)) (mem_range_self κ) hj
  choose V hV hSV η hη hηO using fun i =>
    exists_cutoff (isCompact_fixedSet sz w i).isClosed (hO i) (hsub i)
  refine ⟨V, hV, hSV, η, hη, ?_, ?_⟩
  · intro i j hij
    exact Set.disjoint_left.mpr fun y hy hj => (hηO i hy).2 (mem_iUnion.mpr ⟨⟨j, hij.symm⟩, hj⟩)
  · intro i κ X hx
    apply hUX κ X
    have hh := (hηO i hx).1
    change compactFrame sz κ X * w i * (w i)⁻¹ ∈ U at hh
    rwa [mul_inv_cancel_right] at hh

set_option maxHeartbeats 550000 in
private theorem eventually_split_trace (g : G) (w : ι → K) (W : C(K × H, ℂ))
    (V : ι → Set K) (η : ι → C(K, ℂ))
    (hV : ∀ i, IsOpen (V i)) (hSV : ∀ i, fixedSet sz w i ⊆ V i) (hη : ∀ i, EqOn (η i) 1 (V i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (tsupport (η i)) (fixedSet sz w j))
    (hfix : ∀ y h, testArgument sz g (y, h) = 1 → ∃ i, y ∈ fixedSet sz w i)
    (φ : ℝ → C(K, ℂ)) (hφ : ∀ U : Set K, IsOpen U → 1 ∈ U →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), Function.support (φ ε) ⊆ U) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), weightedIntegral sz g W (φ ε) =
      ∑ i, weightedIntegral sz g (patchWeight sz (η i) W) (φ ε) := by
  classical
  let O (i : ι) := V i ∩ ⋂ j : {j : ι // j ≠ i}, (tsupport (η j))ᶜ
  have hO (i : ι) : IsOpen (O i) := (hV i).inter
    (isOpen_iInter_of_finite fun j => (isClosed_tsupport (η j)).isOpen_compl)
  have hSO (i : ι) : fixedSet sz w i ⊆ O i := by
    intro y hy
    exact ⟨hSV i hy, mem_iInter.mpr fun j hc => (Set.disjoint_left.mp (hdisj j i j.2)) hc hy⟩
  let U := ⋃ i, O i
  let B := (Prod.fst : K × H → K) ⁻¹' Uᶜ
  have hB : IsCompact B := ((isOpen_iUnion hO).isClosed_compl.preimage continuous_fst).isCompact
  have hB₀ (p : K × H) (hp : p ∈ B) : testArgument sz g p ≠ 1 := by
    intro h
    obtain ⟨i, hi⟩ := hfix p.1 p.2 h
    exact hp (mem_iUnion.mpr ⟨i, hSO i hi⟩)
  filter_upwards [eventually_vanish_on hB (continuous_testArgument sz g) hB₀ φ hφ] with ε he
  have hsum (y : K) (hy : y ∈ U) : ∑ i, η i y = 1 := by
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    rw [Finset.sum_eq_single i]
    · exact hη i hi.1
    · intro j _ hji
      by_contra hh
      exact (mem_iInter.mp hi.2 ⟨j, hji⟩) (subset_tsupport _ hh)
    · simp
  have hpoint (y : K) (h : H) : W (y, h) * φ ε (testArgument sz g (y, h)) =
      ∑ i, patchIntegrand sz g (η i) W (φ ε) (y, h) := by
    simp only [patchIntegrand, patchWeight, ContinuousMap.coe_mk, mul_assoc,
      ← Finset.sum_mul]
    by_cases hy : y ∈ U
    · rw [hsum y hy, one_mul]
    · rw [he (y, h) hy, mul_zero, mul_zero]
  let F (i : ι) : C(K × H, ℂ) := ⟨patchIntegrand sz g (η i) W (φ ε), continuous_patchIntegrand ..⟩
  have hint (y : K) (i : ι) : Integrable (fun h => F i (y, h)) (frameMeasure sz) :=
    ((F i).continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hin (i : ι) : Integrable (fun y => ∫ h, F i (y, h) ∂frameMeasure sz) (compactHaar N) :=
    (continuous_inner sz (F i)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (∫ y, ∫ h, W (y, h) * φ ε (testArgument sz g (y, h)) ∂frameMeasure sz ∂compactHaar N) =
    ∑ i, ∫ y, ∫ h, F i (y, h) ∂frameMeasure sz ∂compactHaar N
  simp_rw [hpoint, ← show ∀ i p, F i p = patchIntegrand sz g (η i) W (φ ε) p from fun _ _ => rfl,
    integral_finsetSum _ (fun i _ => hint _ i), integral_finsetSum _ (fun i _ => hin i)]

/-- The local weight, including the chart density and the spatial cutoff. -/
def localizedWeight (w : K) (R : H) (η : C(K, ℂ)) (W : C(K × H, ℂ)) (κ : H) (z : E) : ℂ :=
  chartWeight sz z.1 * (η (placedFrame sz w κ z.1) *
    W (placedFrame sz w κ z.1, placedLeftFrame sz R κ z.2))

set_option maxHeartbeats 500000 in
theorem continuous_localizedWeight (w : K) (R : H) (η : C(K, ℂ)) (W : C(K × H, ℂ)) :
    Continuous (Function.uncurry (localizedWeight sz w R η W)) := by
  have hκ : Continuous (Prod.fst : H × E → H) := continuous_fst
  have he : Continuous (Prod.snd : H × E → E) := continuous_snd
  have hX : Continuous (Prod.fst : E → XSpace) := continuous_fst
  have hZ : Continuous (Prod.snd : E → ZSpace) := continuous_snd
  have hy := (continuous_placedFrame sz w).comp (hκ.prodMk (hX.comp he))
  have hh := (continuous_placedLeftFrame sz R).comp (hκ.prodMk (hZ.comp he))
  have hf := ((continuous_chartWeight sz).comp (hX.comp he)).mul
    ((η.continuous.comp hy).mul (W.continuous.comp (hy.prodMk hh)))
  convert hf using 1
  rfl

end Setup

section Patch

variable {c : ℕ} (sz : Fin c → ℕ)

local notation "N" => ∑ i, sz i
local notation "K" => Ortho N
local notation "G" => Langlands.GeneralLinear N ℝ
local notation "H" => LeviFrame sz
local notation "XSpace" => (Coord sz → ℝ)
local notation "ZSpace" => (WithinIndex sz → ℝ)
local notation "E" => (XSpace × ZSpace)

local notation "CX" => closedBall (0 : XSpace) 1
local notation "CZ" => closedBall (0 : ZSpace) Real.pi

set_option maxHeartbeats 900000 in
private theorem eventually_local_patch (g : G) (w : K) (R : H) (η : C(K, ℂ)) (W : C(K × H, ℂ))
    (hsize : ∀ i, sz i = 1 ∨ sz i = 2)
    (hX : ∀ κ X, placedFrame sz w κ X ∈ tsupport η → ‖X‖ < 1)
    (hfix : ∀ y h, y ∈ tsupport η → testArgument sz g (y, h) = 1 →
      y ∈ range (fun κ => blockFrame sz κ * w))
    (hcenter : ∀ κ h, testArgument sz g (blockFrame sz κ * w, h) = 1 ↔ h = fixedLeftFrame sz R κ)
    (C : ℝ) (hC : ∀ ψ : C(K, ℂ), (∫ y, ψ y ∂compactHaar N) =
      (C : ℂ) * ∫ p : H × XSpace, chartWeight sz p.2 * ψ (compactFrame sz p.1 p.2) ∂chartMeasure sz)
    (φ : ℝ → C(K, ℂ)) (hφ : ∀ U : Set K, IsOpen U → 1 ∈ U →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), Function.support (φ ε) ⊆ U)
    (r : ℝ) (hr : 0 < r) (hrX : r ≤ 1) (hrZ : r ≤ Real.pi) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), weightedIntegral sz g (patchWeight sz η W) (φ ε) =
      (C : ℂ) * (frameCoefficient sz : ℂ) * (∫ κ, ∫ z in closedBall (0 : E) r,
        localizedWeight sz w R η W κ z * φ ε (placedArgument sz g w R κ z) ∂volume ∂frameMeasure sz) := by
  let Y (p : H × XSpace) := placedFrame sz w p.1 p.2
  have hY : Continuous Y := continuous_placedFrame sz w
  let A (p : (H × XSpace) × H) := testArgument sz g (Y p.1, p.2 * fixedLeftFrame sz R p.1.1)
  have hA : Continuous A := by
    have hκ : Continuous (fun p : (H × XSpace) × H => p.1.1) := continuous_fst.fst
    have h := continuous_snd.mul ((continuous_fixedLeftFrame sz R).comp hκ)
    exact (continuous_testArgument sz g).comp ((hY.comp continuous_fst).prodMk h)
  let S : Set ((H × XSpace) × H) :=
    (((univ : Set H) ×ˢ CX) ×ˢ (positiveFrame sz)ᶜ) ∩
      (Y ∘ Prod.fst) ⁻¹' tsupport η
  have hS : IsCompact S := ((isCompact_univ.prod (isCompact_closedBall _ _)).prod
    (isClopen_positiveFrame sz).2.isClosed_compl.isCompact).inter_right
      ((isClosed_tsupport η).preimage (hY.comp continuous_fst))
  have hS₀ (p : (H × XSpace) × H) (hp : p ∈ S) : A p ≠ 1 := by
    intro h
    have hy := hfix _ _ hp.2 h
    have hx : p.1.2 = 0 := lower_eq_zero_of_placedFrame_mem sz w _ _ hy
    have hcenter' : testArgument sz g (blockFrame sz p.1.1 * w, p.2 * fixedLeftFrame sz R p.1.1) = 1 := by
      change testArgument sz g (placedFrame sz w p.1.1 p.1.2, _) = 1 at h
      rwa [hx, placedFrame_zero] at h
    have he := (hcenter p.1.1 _).mp hcenter'
    have hg : p.2 = 1 := mul_right_cancel (he.trans (one_mul _).symm)
    exact hp.1.2 (hg.symm ▸ one_mem_positiveFrame sz)
  let Q : Set E := CX ×ˢ CZ
  let U : Set (H × E) := ((univ : Set H) ×ˢ Q) ∩
    ((fun p : H × E => Y (p.1, p.2.1)) ⁻¹' tsupport η) ∩ {p | r ≤ ‖p.2‖}
  have hKY : Continuous (fun p : H × E => Y (p.1, p.2.1)) := by
    have hκ : Continuous (Prod.fst : H × E → H) := continuous_fst
    have he : Continuous (Prod.snd : H × E → E) := continuous_snd
    have hX' : Continuous (Prod.fst : E → XSpace) := continuous_fst
    simpa only [Function.comp_def] using hY.comp (hκ.prodMk (hX'.comp he))
  have hQ : IsCompact Q := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hU : IsCompact U := ((isCompact_univ.prod hQ).inter_right
    ((isClosed_tsupport η).preimage hKY)).inter_right (isClosed_le continuous_const continuous_snd.norm)
  have hU₀ (p : H × E) (hp : p ∈ U) : placedArgument sz g w R p.1 p.2 ≠ 1 := by
    intro h
    have hy := hfix _ _ hp.1.2 h
    have hx : p.2.1 = 0 := lower_eq_zero_of_placedFrame_mem sz w _ _ hy
    have he : testArgument sz g (blockFrame sz p.1 * w, placedLeftFrame sz R p.1 p.2.2) = 1 := by
      change testArgument sz g (placedFrame sz w p.1 p.2.1, _) = 1 at h
      rwa [hx, placedFrame_zero] at h
    have hangle : angularFrame sz p.2.2 = 1 := by
      have hleft := (hcenter p.1 _).mp he
      exact mul_right_cancel (hleft.trans (one_mul _).symm)
    have hz := (angularFrame_eq_one_iff sz hsize _ hp.1.1.2.2).mp hangle
    have hpz : p.2 = 0 := Prod.ext hx hz
    have hle : r ≤ ‖p.2‖ := hp.2
    rw [hpz, norm_zero] at hle
    exact (not_lt_of_ge hle) hr
  filter_upwards [eventually_vanish_on hS hA hS₀ φ hφ,
    eventually_vanish_on hU (continuous_placedArgument sz g w R) hU₀ φ hφ] with ε hεS hεU
  let F : C(K × H, ℂ) := ⟨patchIntegrand sz g η W (φ ε), continuous_patchIntegrand ..⟩
  let I (y : K) : ℂ := ∫ h, F (y, h) ∂frameMeasure sz
  have hI : Continuous I := continuous_inner sz F
  let ψ : C(K, ℂ) := ⟨fun y => I (y * w), hI.comp (continuous_id.mul continuous_const)⟩
  let P (p : H × XSpace) := chartWeight sz p.2 * I (Y p)
  have hP : Continuous P := ((continuous_chartWeight sz).comp continuous_snd).mul (hI.comp hY)
  have hintP : Integrable P ((frameMeasure sz).prod (volume.restrict CX)) := by
    rw [← Measure.restrict_univ (μ := frameMeasure sz), Measure.prod_restrict]
    exact hP.continuousOn.integrableOn_compact (isCompact_univ.prod (isCompact_closedBall _ _))
  have hpchart : (∫ p, P p ∂chartMeasure sz) =
      ∫ κ, ∫ X in CX, P (κ, X) ∂volume ∂frameMeasure sz := by
    rw [← integral_prod _ hintP, ← Measure.restrict_univ (μ := frameMeasure sz), Measure.prod_restrict]
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => ?_)).symm
    have hXout : p.2 ∉ CX := fun h => hp ⟨mem_univ _, h⟩
    have hη : η (Y p) = 0 := by
      by_contra hn
      have hb := hX p.1 p.2 (subset_tsupport _ hn)
      exact hXout (mem_closedBall_zero_iff.mpr hb.le)
    simp [P, I, F, patchIntegrand, patchWeight, hη]
  let T (p : H × E) := localizedWeight sz w R η W p.1 p.2 * φ ε (placedArgument sz g w R p.1 p.2)
  have hT : Continuous T := (continuous_localizedWeight sz w R η W).mul
    ((φ ε).continuous.comp (continuous_placedArgument sz g w R))
  have hsub : closedBall (0 : E) r ⊆ Q := by
    intro z hz
    rw [mem_closedBall_zero_iff] at hz
    have hn := Prod.norm_def z
    exact ⟨mem_closedBall_zero_iff.mpr ((le_max_left _ _).trans (hn ▸ hz) |>.trans hrX),
      mem_closedBall_zero_iff.mpr ((le_max_right _ _).trans (hn ▸ hz) |>.trans hrZ)⟩
  have hvolume : ((volume : Measure XSpace).prod (volume : Measure ZSpace)) = volume := rfl
  have hlocal (κ : H) : (∫ X in CX, P (κ, X) ∂volume) =
      (frameCoefficient sz : ℂ) * ∫ z in closedBall (0 : E) r, T (κ, z) ∂volume := by
    have hangular (X : XSpace) (hxc : X ∈ CX) : I (Y (κ, X)) =
        (frameCoefficient sz : ℂ) * ∫ Z in CZ, F (Y (κ, X), placedLeftFrame sz R κ Z) ∂volume := by
      let L (h : H) := F (Y (κ, X), h * fixedLeftFrame sz R κ)
      have hL : Continuous L := F.continuous.comp (continuous_const.prodMk (continuous_id.mul continuous_const))
      have htr : I (Y (κ, X)) = ∫ h, L h ∂frameMeasure sz :=
        (integral_mul_right_eq_self (μ := frameMeasure sz) (fun h => F (Y (κ, X), h)) _).symm
      rw [htr, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := positiveFrame sz) (f := L)
        (fun h hh => ?_), realCartanAngularFrame c sz hsize, integral_smul_measure,
        ENNReal.toReal_ofReal (frameCoefficient_pos sz).le, Complex.real_smul]
      · rw [integral_map (continuous_angularFrame sz).aemeasurable hL.aestronglyMeasurable]
        rfl
      · by_cases hy : η (Y (κ, X)) = 0
        · simp [L, F, patchIntegrand, patchWeight, hy]
        · have hS' : ((κ, X), h) ∈ S := ⟨⟨⟨mem_univ _, hxc⟩, hh⟩, subset_tsupport _ hy⟩
          have htest := hεS ((κ, X), h) hS'
          change φ ε (testArgument sz g (Y (κ, X), h * fixedLeftFrame sz R κ)) = 0 at htest
          simp [L, F, patchIntegrand, htest]
    have hTX (X : XSpace) (hx : X ∈ CX) : P (κ, X) =
        (frameCoefficient sz : ℂ) * ∫ Z in CZ, T (κ, X, Z) ∂volume := by
      simp only [P, hangular X hx, ← integral_const_mul]
      congr 1
      funext Z
      simp only [T, localizedWeight, F, patchIntegrand, patchWeight, ContinuousMap.coe_mk, Y,
        placedArgument, testArgument]
      ring
    have hInt : Integrable (fun z : E => T (κ, z)) ((volume.restrict CX).prod (volume.restrict CZ)) := by
      rw [Measure.prod_restrict, hvolume]
      exact (hT.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact hQ
    calc
      _ = (frameCoefficient sz : ℂ) * ∫ X in CX, ∫ Z in CZ, T (κ, X, Z) ∂volume ∂volume := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact (ae_restrict_iff' isClosed_closedBall.measurableSet).mpr (ae_of_all _ hTX)
      _ = (frameCoefficient sz : ℂ) * ∫ z in Q, T (κ, z) ∂volume := by
        rw [← integral_prod _ hInt, Measure.prod_restrict, hvolume]
      _ = _ := by
        congr 1
        refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hQ.measurableSet.nullMeasurableSet hsub
          (ae_of_all _ fun z hz => ?_)
        by_cases hy : η (Y (κ, z.1)) = 0
        · simp [T, localizedWeight, Y] at hy ⊢
          rw [hy]
          simp
        · have hrle : r ≤ ‖z‖ := le_of_lt (lt_of_not_ge (fun hzle =>
            hz.2 (mem_closedBall_zero_iff.mpr hzle)))
          have hU' : (κ, z) ∈ U := ⟨⟨⟨mem_univ _, hz.1⟩, subset_tsupport _ hy⟩, hrle⟩
          simp [T, hεU (κ, z) hU']
  have hψ : (∫ y, ψ y ∂compactHaar N) = ∫ y, I y ∂compactHaar N := by
    rw [compactHaar, integral_map (continuous_compactEquiv N).aemeasurable ψ.continuous.aestronglyMeasurable,
      integral_map (continuous_compactEquiv N).aemeasurable hI.aestronglyMeasurable]
    simpa only [ψ, ContinuousMap.coe_mk, map_mul, MulEquiv.apply_symm_apply] using
      integral_mul_right_eq_self (μ := haarK N) (fun h => I (compactEquiv N h)) ((compactEquiv N).symm w)
  change (∫ y, I y ∂compactHaar N) = _
  calc
    _ = (∫ y, ψ y ∂compactHaar N) := hψ.symm
    _ = (C : ℂ) * ∫ p, P p ∂chartMeasure sz := hC ψ
    _ = _ := by
      rw [hpchart]
      simp_rw [hlocal, integral_const_mul]
      ring

end Patch

/-- Tests concentrating at the identity localize to the fixed flag charts.
The parameter `w` indexes disjoint compact block cosets, and the stated
center equations identify the fixed left frame in each of them. -/
def RealCartanTraceLocalizationStatement : Prop :=
  ∀ (c : ℕ) (sz : Fin c → ℕ),
    let K := Ortho (∑ i, sz i)
    let H := LeviFrame sz
    let E := (Coord sz → ℝ) × (WithinIndex sz → ℝ)
    ∃ C : ℝ, 0 < C ∧
      ∀ (ι : Type) [Fintype ι] (g : Langlands.GeneralLinear (∑ i, sz i) ℝ) (w : ι → K) (R : ι → H),
        (∀ i, sz i = 1 ∨ sz i = 2) →
        Pairwise (fun i j => Disjoint (range (fun κ => blockFrame sz κ * w i))
          (range (fun κ => blockFrame sz κ * w j))) →
        (∀ y h, compactArgument g y (blockFrame sz h) = 1 →
          ∃ i, y ∈ range (fun κ => blockFrame sz κ * w i)) →
        (∀ i κ h, compactArgument g (blockFrame sz κ * w i) (blockFrame sz h) = 1 ↔
          h = fixedLeftFrame sz (R i) κ) →
        ∃ η : ι → C(K, ℂ), (∀ i κ, η i (blockFrame sz κ * w i) = 1) ∧
          ∀ (W : C(K × H, ℂ)) (φ : ℝ → C(K, ℂ)),
            (∀ U : Set K, IsOpen U → 1 ∈ U →
              ∀ᶠ ε in 𝓝[>] (0 : ℝ), Function.support (φ ε) ⊆ U) →
            ∀ r > 0, r ≤ 1 → r ≤ Real.pi →
            ∀ᶠ ε in 𝓝[>] (0 : ℝ), weightedIntegral sz g W (φ ε) =
              (C : ℂ) * (frameCoefficient sz : ℂ) *
                ∑ i, ∫ κ, ∫ z in closedBall (0 : E) r,
                  localizedWeight sz (w i) (R i) (η i) W κ z *
                    φ ε (placedArgument sz g (w i) (R i) κ z) ∂volume ∂frameMeasure sz

set_option maxHeartbeats 800000 in
theorem realCartanTraceLocalization : RealCartanTraceLocalizationStatement := by
  intro c sz K H E
  obtain ⟨C, hCpos, hC⟩ := realLeviCompactChart c sz
  refine ⟨C, hCpos, fun ι _ g w R hsize hdisj hfix hcenter => ?_⟩
  obtain ⟨V, hV, hSV, η, hη, hsep, hX⟩ := exists_coset_cutoffs sz w hdisj
  refine ⟨η, fun i κ => hη i (hSV i (mem_range_self κ)), fun W φ hφ r hr hrX hrZ => ?_⟩
  have hsingle (i : ι) := eventually_local_patch sz g (w i) (R i) (η i) W hsize (hX i)
    (fun y h hy hh => by
      obtain ⟨j, hj⟩ := hfix y h hh
      by_cases he : i = j
      · rwa [he]
      · exact ((Set.disjoint_left.mp (hsep i j he)) hy hj).elim)
    (hcenter i) C hC φ hφ r hr hrX hrZ
  filter_upwards [eventually_split_trace sz g w W V η hV hSV hη hsep hfix φ hφ,
    eventually_all.mpr hsingle] with ε hs hl
  rw [hs]
  simp_rw [hl]
  rw [Finset.mul_sum]

end Langlands.Archimedean.RealCartanTraceLocalization
