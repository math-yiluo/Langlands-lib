import Langlands.HarmonicAnalysis.Bicharacter.SelfDualMeasure

/-!
# Dual Haar measures of a perfect pairing

GKT Appendix 1.A, Theorem 1.37 and Remark 1.38 (pp. 43–44), and the special case (1.12) of a
non-degenerate bilinear pairing of vector spaces (p. 45). Let `X`, `Y` be commutative,
locally compact, second countable groups with arbitrarily large and small compact open subgroups
and `α : X → Y → ℂ` a perfect pairing (`IsPerfectBicharacter`: a bicharacter of modulus one,
locally constant, which identifies each group with the dual of the other, in the form: the
annihilators of large compact sets are small, and the annihilators of neighbourhoods of `0` are
relatively compact). For Haar measures `μ` on `X` and `ν` on `Y` the Fourier transforms are

`ℱ_μ φ (y) = ∫ α(x, y) φ(x) dμ(x)`,  `ℱ'_ν f (x) = ∫ α(x, y) f(y) dν(y)`

(`pairingFourier`, `pairingFourierDual`).

* (a) They preserve the Schwartz–Bruhat functions (`pairingFourier_mem`).
* (d) `ℱ'_ν ℱ_μ φ = C φ(-·)` and `ℱ_μ ℱ'_ν f = C f(-·)` with one constant
  `C = pairingFourierConstant μ ν α > 0` (`pairingFourierDual_pairingFourier_eq`,
  `pairingFourier_pairingFourierDual_eq`).
* (b), (c) `‖ℱ_μ φ‖²_ν = C ‖φ‖²_μ` and `‖ℱ'_ν f‖²_μ = C ‖f‖²_ν`
  (`lintegral_enorm_pairingFourier_sq`, `lintegral_enorm_pairingFourierDual_sq`).
* The **dual measure** `pairingDualMeasure μ α = C⁻¹ ν` (independent of `ν`) is the unique Haar
  measure on `Y` for which the inversion formula holds and `ℱ_μ` is an isometry;
  `(rμ)' = r⁻¹ μ'` and the dual of `μ'` for the flipped pairing is `μ` (Remark 1.38).

The constant is computed on the indicator of a compact open subgroup `A = M^⊥` (`M ⊆ Y` compact
open): its transform is `μ(A)` times the indicator of `A^⊥`, and `A^⊥⊥ = A`, so `C = μ(A) ν(A^⊥)`.
For a self-dual bicharacter (`H = G`) this is the theory of
`Langlands.HarmonicAnalysis.Bicharacter.SelfDualMeasure` (`pairingFourier_eq_bicharacterFourier`,
`pairingDualMeasure_eq_bicharacterDualMeasure`). For a non-degenerate pairing `⟨,⟩ : X × Y → F`
of finite-dimensional vector spaces over a nonarchimedean local field and a non-trivial character
`ψ`, `ψ ∘ ⟨,⟩` is perfect (`isPerfectBicharacter_of_nondegenerate`).
-/

noncomputable section

open MeasureTheory
open scoped Topology NNReal ENNReal

namespace Langlands.HarmonicAnalysis

/-- A **perfect pairing** `α : X × Y → ℂ¹` of commutative topological groups (GKT Appendix 1.A): a
bicharacter of modulus one, locally constant on `X × Y`, such that the annihilator in either group
of a large compact subset of the other is contained in a given neighbourhood of `0` (`small_left`,
`small_right`) and the annihilator of a neighbourhood of `0` is contained in a compact set
(`big_left`, `big_right`). -/
structure IsPerfectBicharacter {X Y : Type*} [AddCommGroup X] [TopologicalSpace X]
    [AddCommGroup Y] [TopologicalSpace Y] (α : X → Y → ℂ) : Prop where
  map_add_left : ∀ x x' y, α (x + x') y = α x y * α x' y
  map_add_right : ∀ x y y', α x (y + y') = α x y * α x y'
  norm_eq_one : ∀ x y, ‖α x y‖ = 1
  isLocallyConstant : IsLocallyConstant fun p : X × Y => α p.1 p.2
  small_left : ∀ U ∈ 𝓝 (0 : Y), ∃ K : Set X, IsCompact K ∧ ∀ y, (∀ x ∈ K, α x y = 1) → y ∈ U
  big_left : ∀ U ∈ 𝓝 (0 : X), ∃ K : Set Y, IsCompact K ∧ ∀ y, (∀ x ∈ U, α x y = 1) → y ∈ K
  small_right : ∀ U ∈ 𝓝 (0 : X), ∃ K : Set Y, IsCompact K ∧ ∀ x, (∀ y ∈ K, α x y = 1) → x ∈ U
  big_right : ∀ U ∈ 𝓝 (0 : Y), ∃ K : Set X, IsCompact K ∧ ∀ x, (∀ y ∈ U, α x y = 1) → x ∈ K

namespace IsPerfectBicharacter

variable {X Y : Type*} [AddCommGroup X] [TopologicalSpace X] [AddCommGroup Y] [TopologicalSpace Y]
  {α : X → Y → ℂ}

/-- The flipped pairing `(y, x) ↦ α(x, y)` is perfect. -/
theorem flip (h : IsPerfectBicharacter α) : IsPerfectBicharacter fun y x => α x y where
  map_add_left y y' x := h.map_add_right x y y'
  map_add_right y x x' := h.map_add_left x x' y
  norm_eq_one y x := h.norm_eq_one x y
  isLocallyConstant := h.isLocallyConstant.comp_continuous continuous_swap
  small_left := h.small_right
  big_left := h.big_right
  small_right := h.small_left
  big_right := h.big_left

theorem ne_zero (h : IsPerfectBicharacter α) (x : X) (y : Y) : α x y ≠ 0 := by
  intro h0
  have h1 := h.norm_eq_one x y
  rw [h0, norm_zero] at h1
  exact zero_ne_one h1

theorem map_zero_left (h : IsPerfectBicharacter α) (y : Y) : α 0 y = 1 := by
  have h1 := h.map_add_left 0 0 y
  rw [add_zero] at h1
  exact mul_left_cancel₀ (h.ne_zero 0 y) (by rw [mul_one]; exact h1.symm)

theorem map_neg_left (h : IsPerfectBicharacter α) (x : X) (y : Y) : α (-x) y * α x y = 1 := by
  rw [← h.map_add_left, neg_add_cancel, h.map_zero_left]

theorem conj_apply (h : IsPerfectBicharacter α) (x : X) (y : Y) :
    starRingEnd ℂ (α x y) = α (-x) y := by
  have h2 : starRingEnd ℂ (α x y) * α x y = 1 := by
    rw [Complex.conj_mul', h.norm_eq_one]; simp
  exact mul_right_cancel₀ (h.ne_zero x y) (h2.trans (h.map_neg_left x y).symm)

/-- `α(-x, y) = α(x, -y)`. -/
theorem map_neg_left_eq_map_neg_right (h : IsPerfectBicharacter α) (x : X) (y : Y) :
    α (-x) y = α x (-y) := by
  have h1 := h.map_neg_left x y
  have h2 := h.flip.map_neg_left y x
  exact mul_right_cancel₀ (h.ne_zero x y) (h1.trans h2.symm)

theorem continuous (h : IsPerfectBicharacter α) : Continuous fun p : X × Y => α p.1 p.2 :=
  h.isLocallyConstant.continuous

/-- The annihilator `{y | ∀ x ∈ L, α x y = 1}` in `Y` of a set `L ⊆ X`, as a subgroup. -/
def annihilator (h : IsPerfectBicharacter α) (L : Set X) : AddSubgroup Y where
  carrier := {y | ∀ x ∈ L, α x y = 1}
  zero_mem' := fun x _ => h.flip.map_zero_left x
  add_mem' := fun {a b} ha hb x hx => by rw [h.map_add_right, ha x hx, hb x hx, one_mul]
  neg_mem' := fun {a} ha x hx => by
    have h1 := h.flip.map_neg_left a x
    rw [ha x hx, mul_one] at h1
    exact h1

theorem mem_annihilator (h : IsPerfectBicharacter α) {L : Set X} {y : Y} :
    y ∈ h.annihilator L ↔ ∀ x ∈ L, α x y = 1 := Iff.rfl

/-- The annihilator of a compact set is open. -/
theorem isOpen_annihilator [IsTopologicalAddGroup Y] (h : IsPerfectBicharacter α) {L : Set X}
    (hL : IsCompact L) : IsOpen (h.annihilator L : Set Y) := by
  have hS : IsOpen {p : X × Y | α p.1 p.2 = 1} := h.isLocallyConstant.isOpen_fiber 1
  have hsub : L ×ˢ ({0} : Set Y) ⊆ {p : X × Y | α p.1 p.2 = 1} := by
    rintro ⟨x, y⟩ ⟨_, hy⟩
    simp only [Set.mem_singleton_iff] at hy
    subst hy
    exact h.flip.map_zero_left x
  obtain ⟨u, v, -, hv, hLu, h0v, huv⟩ := generalized_tube_lemma hL isCompact_singleton hS hsub
  apply AddSubgroup.isOpen_of_mem_nhds (g := 0)
  refine Filter.mem_of_superset (hv.mem_nhds (h0v (Set.mem_singleton 0))) ?_
  intro y hy x hx
  exact huv (show (x, y) ∈ u ×ˢ v from ⟨hLu hx, hy⟩)

/-- The annihilator of a compact neighbourhood of `0` is compact and open. -/
theorem isCompact_annihilator [IsTopologicalAddGroup Y] (h : IsPerfectBicharacter α) {L : Set X}
    (hL : IsCompact L) (hL0 : L ∈ 𝓝 (0 : X)) : IsCompact (h.annihilator L : Set Y) := by
  obtain ⟨K, hK, hKL⟩ := h.big_left L hL0
  exact hK.of_isClosed_subset (AddSubgroup.isClosed_of_isOpen _ (h.isOpen_annihilator hL))
    fun y hy => hKL y hy

end IsPerfectBicharacter

/-! ### The Fourier transforms -/

section Fourier

variable {X Y : Type*} [AddCommGroup X] [TopologicalSpace X] [AddCommGroup Y] [TopologicalSpace Y]

/-- The Fourier transform `ℱ_μ φ (y) = ∫ α(x, y) φ(x) dμ(x)` of a function on `X` (GKT
Appendix 1.A, `F_{dg}`). -/
def pairingFourier [MeasurableSpace X] (μ : Measure X) (α : X → Y → ℂ) (φ : X → ℂ) : Y → ℂ :=
  fun y => ∫ x, α x y * φ x ∂μ

/-- The Fourier transform `ℱ'_ν f (x) = ∫ α(x, y) f(y) dν(y)` of a function on `Y` (GKT
Appendix 1.A, `F_{dh}`): the transform `pairingFourier` of the flipped pairing. -/
def pairingFourierDual [MeasurableSpace Y] (ν : Measure Y) (α : X → Y → ℂ) (f : Y → ℂ) : X → ℂ :=
  pairingFourier ν (fun y x => α x y) f

omit [AddCommGroup X] [TopologicalSpace X] [AddCommGroup Y] [TopologicalSpace Y] in
theorem pairingFourier_apply [MeasurableSpace X] (μ : Measure X) (α : X → Y → ℂ) (φ : X → ℂ)
    (y : Y) : pairingFourier μ α φ y = ∫ x, α x y * φ x ∂μ := rfl

omit [AddCommGroup X] [TopologicalSpace X] [AddCommGroup Y] [TopologicalSpace Y] in
theorem pairingFourierDual_apply [MeasurableSpace Y] (ν : Measure Y) (α : X → Y → ℂ) (f : Y → ℂ)
    (x : X) : pairingFourierDual ν α f x = ∫ y, α x y * f y ∂ν := rfl

omit [AddCommGroup X] [TopologicalSpace X] [AddCommGroup Y] [TopologicalSpace Y] in
theorem pairingFourier_const_mul [MeasurableSpace X] (μ : Measure X) (α : X → Y → ℂ) (c : ℂ)
    (φ : X → ℂ) (y : Y) :
    pairingFourier μ α (fun x => c * φ x) y = c * pairingFourier μ α φ y := by
  simp only [pairingFourier, mul_left_comm (α _ y) c]
  exact integral_const_mul c _

omit [AddCommGroup X] [TopologicalSpace X] [AddCommGroup Y] [TopologicalSpace Y] in
theorem pairingFourier_smul_measure [MeasurableSpace X] (μ : Measure X) (α : X → Y → ℂ) (r : ℝ≥0)
    (φ : X → ℂ) (y : Y) :
    pairingFourier (r • μ) α φ y = ((r : ℝ) : ℂ) * pairingFourier μ α φ y := by
  simp only [pairingFourier, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

end Fourier

namespace PairingFourier.Internal

variable {X Y : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [MeasurableSpace X] [BorelSpace X] [AddCommGroup Y] [TopologicalSpace Y]
  [IsTopologicalAddGroup Y] {α : X → Y → ℂ} (μ : Measure X) [μ.IsAddHaarMeasure]

open BicharacterFourier.Internal

omit [IsTopologicalAddGroup Y] in
theorem pairingFourier_eq_zero (h : IsPerfectBicharacter α) {M : Set X} {f : X → ℂ}
    (hs : ∀ t ∈ M, ∀ x, f (x + t) = f x) {y : Y} (hy : y ∉ h.annihilator M) :
    pairingFourier μ α f y = 0 := by
  have hy' : ¬ ∀ t ∈ M, α t y = 1 := hy
  simp only [not_forall] at hy'
  obtain ⟨t, ht, hne⟩ := hy'
  have key : pairingFourier μ α f y = α t y * pairingFourier μ α f y := by
    simp only [pairingFourier]
    calc ∫ z, α z y * f z ∂μ = ∫ z, α (t + z) y * f (t + z) ∂μ :=
          (integral_add_left_eq_self (fun z => α z y * f z) t).symm
      _ = ∫ z, α t y * (α z y * f z) ∂μ := by
          congr 1; ext z
          rw [h.map_add_left, add_comm t z, hs t ht z]; ring
      _ = α t y * ∫ z, α z y * f z ∂μ := integral_const_mul _ _
  by_contra h0
  exact hne (mul_right_cancel₀ h0 (key.symm.trans (one_mul _).symm))

omit [IsTopologicalAddGroup Y] in
theorem pairingFourier_indicator (h : IsPerfectBicharacter α) (L : AddSubgroup X)
    (ho : IsOpen (L : Set X)) (y : Y) :
    pairingFourier μ α ((L : Set X).indicator fun _ => (1 : ℂ)) y =
      (h.annihilator L : Set Y).indicator (fun _ => (μ.real (L : Set X) : ℂ)) y := by
  by_cases hy : y ∈ (h.annihilator L : Set Y)
  · rw [Set.indicator_of_mem hy]
    have hy' : ∀ x ∈ (L : Set X), α x y = 1 := hy
    simp only [pairingFourier]
    have e : (fun z => α z y * (L : Set X).indicator (fun _ => (1 : ℂ)) z) =
        (L : Set X).indicator (fun _ => (1 : ℂ)) := by
      ext z
      by_cases hz : z ∈ (L : Set X)
      · rw [Set.indicator_of_mem hz, mul_one, hy' z hz]
      · rw [Set.indicator_of_notMem hz, mul_zero]
    rw [e, integral_indicator_const _ ho.measurableSet]
    simp
  · rw [Set.indicator_of_notMem hy]
    exact pairingFourier_eq_zero μ h (indicator_invariant L 1) hy

variable [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace Y] [BorelSpace Y]
  [LocallyCompactSpace Y] [SecondCountableTopology Y] (ν : Measure Y) [ν.IsAddHaarMeasure]

theorem exists_of_annihilator_invariant (h : IsPerfectBicharacter α) (M : AddSubgroup Y)
    (hMc : IsCompact (M : Set Y)) (hMo : IsOpen (M : Set Y)) :
    ∃ C : ℝ, 0 < C ∧ ∀ φ ∈ schwartzBruhatSubmodule X,
      (∀ t ∈ h.flip.annihilator (M : Set Y), ∀ x, φ (x + t) = φ x) →
      ∀ w, pairingFourierDual ν α (pairingFourier μ α φ) w = (C : ℂ) * φ (-w) := by
  set A := h.flip.annihilator (M : Set Y) with hA
  set B := h.annihilator (A : Set X) with hB
  have hAo : IsOpen (A : Set X) := h.flip.isOpen_annihilator hMc
  have hAc : IsCompact (A : Set X) :=
    h.flip.isCompact_annihilator hMc (hMo.mem_nhds M.zero_mem)
  have hBo : IsOpen (B : Set Y) := h.isOpen_annihilator hAc
  have hBc : IsCompact (B : Set Y) := h.isCompact_annihilator hAc (hAo.mem_nhds A.zero_mem)
  have hMB : (M : Set Y) ⊆ B := fun y hy x hx => hx y hy
  have hBA : (h.flip.annihilator (B : Set Y) : Set X) = A := by
    ext z
    constructor
    · intro hz y hy
      exact hz y (hMB hy)
    · intro hz y hy
      exact hy z hz
  have hApos : 0 < μ.real (A : Set X) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (hAo.measure_pos μ ⟨0, A.zero_mem⟩).ne' hAc.measure_lt_top.ne
  have hBpos : 0 < ν.real (B : Set Y) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (hBo.measure_pos ν ⟨0, B.zero_mem⟩).ne' hBc.measure_lt_top.ne
  refine ⟨μ.real (A : Set X) * ν.real (B : Set Y), mul_pos hApos hBpos, fun φ hφ hs w => ?_⟩
  have hφ' : IsLocallyConstant φ ∧ HasCompactSupport φ := hφ
  have hSc : IsCompact (tsupport φ) := hφ'.2.isCompact
  have : IsFiniteMeasure (μ.restrict (tsupport φ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hSc.measure_lt_top⟩
  have : IsFiniteMeasure (ν.restrict (B : Set Y)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hBc.measure_lt_top⟩
  have h1 : ∀ y, ∫ z, α z y * φ z ∂μ = ∫ z in tsupport φ, α z y * φ z ∂μ := fun y =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
      rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]).symm
  have h2 : ∫ y, α w y * ∫ z, α z y * φ z ∂μ ∂ν =
      ∫ y in (B : Set Y), α w y * ∫ z, α z y * φ z ∂μ ∂ν :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
      have h0 := pairingFourier_eq_zero μ h hs (y := y) hy
      simp only [pairingFourier] at h0
      rw [h0, mul_zero]).symm
  have h3 : ∀ y, α w y * ∫ z in tsupport φ, α z y * φ z ∂μ =
      ∫ z in tsupport φ, α w y * (α z y * φ z) ∂μ := fun y => (integral_const_mul _ _).symm
  obtain ⟨C0, hC0⟩ := hφ'.1.continuous.bounded_above_of_compact_support hφ'.2
  have hcont : Continuous (Function.uncurry fun y z => α w y * (α z y * φ z)) :=
    ((h.continuous.comp (continuous_const.prodMk continuous_fst))).mul
      ((h.continuous.comp (continuous_snd.prodMk continuous_fst)).mul
        (hφ'.1.continuous.comp continuous_snd))
  have hint : Integrable (Function.uncurry fun y z => α w y * (α z y * φ z))
      ((ν.restrict (B : Set Y)).prod (μ.restrict (tsupport φ))) :=
    (integrable_const C0).mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun p => by
      simp only [Function.uncurry, norm_mul, h.norm_eq_one, one_mul]
      exact hC0 p.2)
  have h4 : ∀ z, ∫ y in (B : Set Y), α w y * (α z y * φ z) ∂ν =
      φ z * (h.flip.annihilator (B : Set Y) : Set X).indicator
        (fun _ => (ν.real (B : Set Y) : ℂ)) (w + z) := by
    intro z
    have hB1 := pairingFourier_indicator ν h.flip B hBo (w + z)
    simp only [pairingFourier] at hB1
    rw [← hB1, ← integral_indicator hBo.measurableSet, mul_comm (φ z), ← integral_mul_const]
    congr 1
    ext y
    by_cases hy : y ∈ (B : Set Y)
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, h.map_add_left]
      ring
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
      ring
  have h5 : ∀ z, φ z * (h.flip.annihilator (B : Set Y) : Set X).indicator
      (fun _ => (ν.real (B : Set Y) : ℂ)) (w + z) =
      φ (-w) * (h.flip.annihilator (B : Set Y) : Set X).indicator
        (fun _ => (ν.real (B : Set Y) : ℂ)) (w + z) := by
    intro z
    by_cases hz : w + z ∈ (h.flip.annihilator (B : Set Y) : Set X)
    · have hzA : w + z ∈ (A : Set X) := hBA.subset hz
      have e := hs (w + z) hzA (-w)
      rw [neg_add_cancel_left] at e
      rw [e]
    · rw [Set.indicator_of_notMem hz, mul_zero, mul_zero]
  have h6 : ∫ z in tsupport φ, φ (-w) * (h.flip.annihilator (B : Set Y) : Set X).indicator
      (fun _ => (ν.real (B : Set Y) : ℂ)) (w + z) ∂μ =
      ∫ z, φ (-w) * (h.flip.annihilator (B : Set Y) : Set X).indicator
        (fun _ => (ν.real (B : Set Y) : ℂ)) (w + z) ∂μ := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_
    rw [← h5 z, image_eq_zero_of_notMem_tsupport hz, zero_mul]
  have hAm : MeasurableSet (h.flip.annihilator (B : Set Y) : Set X) := by
    rw [hBA]
    exact hAo.measurableSet
  simp only [pairingFourierDual, pairingFourier]
  rw [h2]
  simp_rw [h1, h3]
  rw [integral_integral_swap hint]
  simp_rw [h4, h5]
  rw [h6, integral_const_mul,
    integral_add_left_eq_self (fun z => (h.flip.annihilator (B : Set Y) : Set X).indicator
      (fun _ => (ν.real (B : Set Y) : ℂ)) z) w,
    integral_indicator_const _ hAm, hBA, Complex.real_smul]
  push_cast
  ring

theorem exists_of_invariant [CompactOpenExhaustion Y] (h : IsPerfectBicharacter α)
    (N : AddSubgroup X) (hNo : IsOpen (N : Set X)) :
    ∃ C : ℝ, 0 < C ∧ ∀ φ ∈ schwartzBruhatSubmodule X, (∀ t ∈ N, ∀ x, φ (x + t) = φ x) →
      ∀ w, pairingFourierDual ν α (pairingFourier μ α φ) w = (C : ℂ) * φ (-w) := by
  obtain ⟨K, hK, hKN⟩ := h.small_right (N : Set X) (hNo.mem_nhds N.zero_mem)
  obtain ⟨M, hMc, hMo, hKM⟩ := CompactOpenExhaustion.exists_superset K hK
  obtain ⟨C, hC, hCφ⟩ := exists_of_annihilator_invariant μ ν h M hMc hMo
  refine ⟨C, hC, fun φ hφ hs => hCφ φ hφ fun t ht => hs t (hKN t fun y hy => ?_)⟩
  exact ht y (hKM hy)

end PairingFourier.Internal

open PairingFourier.Internal BicharacterFourier.Internal

section Inversion

variable {X Y : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [LocallyCompactSpace Y]
  [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {α : X → Y → ℂ}

omit [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace Y] [BorelSpace Y]
  [LocallyCompactSpace Y] [SecondCountableTopology Y] in
/-- **The Fourier transform preserves Schwartz–Bruhat functions** (GKT Theorem 1.37 (a)). -/
theorem pairingFourier_mem (μ : Measure X) [μ.IsAddHaarMeasure] (h : IsPerfectBicharacter α)
    {φ : X → ℂ} (hφ : φ ∈ schwartzBruhatSubmodule X) :
    pairingFourier μ α φ ∈ schwartzBruhatSubmodule Y := by
  obtain ⟨K, hK, hKm⟩ := h.big_left _ (eventually_add_eq_of_mem_schwartzBruhatSubmodule hφ)
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun y => ?_,
    HasCompactSupport.intro hK fun y hy => ?_⟩
  · have h1 : ∀ᶠ z in 𝓝 y, ∀ x ∈ tsupport φ, α x z = α x y := by
      refine IsCompact.eventually_forall_of_forall_eventually hφ.2 fun x _ => ?_
      have h2 : IsLocallyConstant fun q : Y × X => (α q.2 q.1, α q.2 y) :=
        (h.isLocallyConstant.comp_continuous continuous_swap).prodMk
          (h.isLocallyConstant.comp_continuous (continuous_snd.prodMk continuous_const))
      filter_upwards [h2.eventually_eq (y, x)] with q hq
      simp only [Prod.mk.injEq] at hq
      rw [hq.1, hq.2]
    filter_upwards [h1] with z hz
    unfold pairingFourier
    congr 1
    funext x
    by_cases hx : x ∈ tsupport φ
    · rw [hz x hx]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  · obtain ⟨t, ht, hne⟩ : ∃ t, (∀ x, φ (x + t) = φ x) ∧ α t y ≠ 1 := by
      by_contra hne
      exact hy (hKm y fun t ht => by
        by_contra h4
        exact hne ⟨t, ht, h4⟩)
    have h1 := integral_add_right_eq_self (μ := μ) (fun x => α x y * φ x) t
    have h2 : ∀ x, α (x + t) y * φ (x + t) = α t y * (α x y * φ x) := by
      intro x
      rw [ht, h.map_add_left]; ring
    simp only [h2, integral_const_mul] at h1
    refine (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hne)
    unfold pairingFourier
    rw [sub_mul, h1, one_mul, sub_self]

omit [LocallyCompactSpace Y] [SecondCountableTopology Y] [MeasurableSpace X] [BorelSpace X]
  [LocallyCompactSpace X] [SecondCountableTopology X] in
/-- **The dual Fourier transform preserves Schwartz–Bruhat functions** (GKT Theorem 1.37 (a)). -/
theorem pairingFourierDual_mem (ν : Measure Y) [ν.IsAddHaarMeasure] (h : IsPerfectBicharacter α)
    {f : Y → ℂ} (hf : f ∈ schwartzBruhatSubmodule Y) :
    pairingFourierDual ν α f ∈ schwartzBruhatSubmodule X :=
  pairingFourier_mem ν h.flip hf

variable [CompactOpenExhaustion X] [CompactOpenExhaustion Y]

/-- **Fourier inversion for a perfect pairing** (GKT Theorem 1.37 (d) up to the normalization of
the measures): `ℱ'_ν ℱ_μ φ = C φ(-·)` with `C > 0`. -/
theorem exists_pos_pairingFourierDual_pairingFourier (μ : Measure X) [μ.IsAddHaarMeasure]
    (ν : Measure Y) [ν.IsAddHaarMeasure] (h : IsPerfectBicharacter α) :
    ∃ C : ℝ, 0 < C ∧ ∀ φ ∈ schwartzBruhatSubmodule X, ∀ x,
      pairingFourierDual ν α (pairingFourier μ α φ) x = (C : ℂ) * φ (-x) := by
  obtain ⟨M0, hM0c, hM0o, -⟩ := CompactOpenExhaustion.exists_superset (∅ : Set X) isCompact_empty
  obtain ⟨C, hC, hCφ⟩ := exists_of_invariant μ ν h M0 hM0o
  refine ⟨C, hC, fun φ hφ x => ?_⟩
  obtain ⟨U, hU, hUinv⟩ := exists_nhds_add_eq_of_mem_schwartzBruhatSubmodule hφ
  obtain ⟨M1, -, hM1o, hM1U⟩ := CompactOpenExhaustion.exists_subset U hU
  have hMo : IsOpen ((M1 ⊓ M0 : AddSubgroup X) : Set X) := by
    rw [AddSubgroup.coe_inf]
    exact hM1o.inter hM0o
  obtain ⟨C', -, hC'φ⟩ := exists_of_invariant μ ν h (M1 ⊓ M0) hMo
  have h0 : (0 : X) ∈ (M0 : Set X) := M0.zero_mem
  have hCC : C' = C := by
    have h1 := hCφ _ (indicator_one_mem_schwartzBruhatSubmodule M0 hM0c hM0o)
      (indicator_invariant M0 1) 0
    have h2 := hC'φ _ (indicator_one_mem_schwartzBruhatSubmodule M0 hM0c hM0o)
      (fun t ht => indicator_invariant M0 1 t (AddSubgroup.mem_inf.mp ht).2) 0
    rw [neg_zero, Set.indicator_of_mem h0, mul_one] at h1 h2
    exact_mod_cast h2.symm.trans h1
  rw [← hCC]
  exact hC'φ φ hφ (fun t ht => hUinv M1 hM1U t (AddSubgroup.mem_inf.mp ht).1) x

end Inversion

/-! ### The constant, the second inversion formula and Plancherel -/

section Constant

variable {X Y : Type*} [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X]
  [AddCommGroup Y] [TopologicalSpace Y] [MeasurableSpace Y]

/-- The constant of Fourier inversion for the pairing `α` and the measures `μ`, `ν`: the `C > 0`
with `ℱ'_ν ℱ_μ φ = C φ(-·)` for every Schwartz–Bruhat function `φ`
(`pairingFourierDual_pairingFourier_eq`; `1` when there is none). -/
def pairingFourierConstant (μ : Measure X) (ν : Measure Y) (α : X → Y → ℂ) : ℝ :=
  open Classical in
  if h : ∃ C : ℝ, 0 < C ∧ ∀ φ ∈ schwartzBruhatSubmodule X, ∀ x,
      pairingFourierDual ν α (pairingFourier μ α φ) x = (C : ℂ) * φ (-x) then h.choose
  else 1

/-- **The dual Haar measure** of `μ` for the pairing `α` (GKT Theorem 1.37 (b)): the Haar measure
`ν` on `Y` with `ℱ'_ν ℱ_μ φ = φ(-·)` for every Schwartz–Bruhat function `φ`; it exists and is
unique, and `ℱ_μ` is an isometry `L²(μ) → L²(ν)` for it. -/
def pairingDualMeasure (μ : Measure X) (α : X → Y → ℂ) : Measure Y :=
  open Classical in
  if h : ∃ ν : Measure Y, ν.IsAddHaarMeasure ∧ ∀ φ ∈ schwartzBruhatSubmodule X, ∀ x,
      pairingFourierDual ν α (pairingFourier μ α φ) x = φ (-x) then h.choose
  else 0

omit [AddCommGroup Y] [TopologicalSpace Y] in
theorem pairingFourierConstant_pos (μ : Measure X) (ν : Measure Y) (α : X → Y → ℂ) :
    0 < pairingFourierConstant μ ν α := by
  classical
  unfold pairingFourierConstant
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_pos

end Constant

section Haar

variable {X Y : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [CompactOpenExhaustion X]
  [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [LocallyCompactSpace Y]
  [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactOpenExhaustion Y]
  {α : X → Y → ℂ}

omit [LocallyCompactSpace X] [SecondCountableTopology X] [BorelSpace X] [IsTopologicalAddGroup Y]
  [LocallyCompactSpace Y] [SecondCountableTopology Y] [BorelSpace Y] [CompactOpenExhaustion Y]
  [AddCommGroup Y] [TopologicalSpace Y] in
theorem pairingFourierConstant_eq {μ : Measure X} {ν : Measure Y} {C : ℝ} (hC : 0 < C)
    (h : ∀ φ ∈ schwartzBruhatSubmodule X, ∀ x,
      pairingFourierDual ν α (pairingFourier μ α φ) x = (C : ℂ) * φ (-x)) :
    pairingFourierConstant μ ν α = C := by
  classical
  have hex : ∃ C : ℝ, 0 < C ∧ ∀ φ ∈ schwartzBruhatSubmodule X, ∀ x,
      pairingFourierDual ν α (pairingFourier μ α φ) x = (C : ℂ) * φ (-x) := ⟨C, hC, h⟩
  rw [pairingFourierConstant, dite_eq_left_of_eq_true (eq_true hex)]
  obtain ⟨φ, hφ, h0⟩ := exists_mem_schwartzBruhatSubmodule_apply_zero (X := X)
  have h1 := hex.choose_spec.2 φ hφ 0
  have h2 := h φ hφ 0
  rw [neg_zero, h0, mul_one] at h1 h2
  exact_mod_cast h1.symm.trans h2

/-- **Fourier inversion** for a perfect pairing: `ℱ'_ν ℱ_μ φ (x) = C(μ, ν) φ(-x)`. -/
theorem pairingFourierDual_pairingFourier_eq (h : IsPerfectBicharacter α) (μ : Measure X)
    [μ.IsAddHaarMeasure] (ν : Measure Y) [ν.IsAddHaarMeasure] {φ : X → ℂ}
    (hφ : φ ∈ schwartzBruhatSubmodule X) (x : X) :
    pairingFourierDual ν α (pairingFourier μ α φ) x =
      (pairingFourierConstant μ ν α : ℂ) * φ (-x) := by
  obtain ⟨C, hC, hC'⟩ := exists_pos_pairingFourierDual_pairingFourier μ ν h
  rw [pairingFourierConstant_eq hC hC']
  exact hC' φ hφ x

omit [LocallyCompactSpace Y] [SecondCountableTopology Y] [CompactOpenExhaustion X]
  [CompactOpenExhaustion Y] [IsTopologicalAddGroup Y] [MeasurableSpace Y] [BorelSpace Y] in
/-- `ℱ_μ (φ ∘ (-·)) = (ℱ_μ φ) ∘ (-·)`. -/
theorem pairingFourier_comp_neg (h : IsPerfectBicharacter α) (μ : Measure X)
    [μ.IsAddHaarMeasure] (φ : X → ℂ) (y : Y) :
    pairingFourier μ α (fun x => φ (-x)) y = pairingFourier μ α φ (-y) := by
  simp only [pairingFourier]
  rw [← integral_neg_eq_self]
  congr 1
  funext x
  rw [neg_neg, h.map_neg_left_eq_map_neg_right]

/-- **The second inversion formula, with the same constant** (GKT Theorem 1.37 (d)):
`ℱ_μ ℱ'_ν f = C(μ, ν) f(-·)`. -/
theorem pairingFourier_pairingFourierDual_eq (h : IsPerfectBicharacter α) (μ : Measure X)
    [μ.IsAddHaarMeasure] (ν : Measure Y) [ν.IsAddHaarMeasure] {f : Y → ℂ}
    (hf : f ∈ schwartzBruhatSubmodule Y) (y : Y) :
    pairingFourier μ α (pairingFourierDual ν α f) y =
      (pairingFourierConstant μ ν α : ℂ) * f (-y) := by
  -- the inversion formula of the flipped pairing, with its constant `C'`
  have h' := pairingFourierDual_pairingFourier_eq h.flip ν μ hf y
  change pairingFourier μ α (pairingFourierDual ν α f) y = _ at h'
  rw [h']
  congr 2
  -- `C' = C`: apply `ℱ_μ` to `ℱ'_ν ℱ_μ φ₀ = C φ₀(-·)` for the indicator `φ₀` of a compact open
  -- subgroup `L`, at `0`
  obtain ⟨L, hLc, hLo, -⟩ := CompactOpenExhaustion.exists_superset (∅ : Set X) isCompact_empty
  have hφ := indicator_one_mem_schwartzBruhatSubmodule L hLc hLo
  have hFφ := pairingFourier_mem μ h hφ
  have e1 := pairingFourierDual_pairingFourier_eq h.flip ν μ hFφ 0
  change pairingFourier μ α (pairingFourierDual ν α (pairingFourier μ α _)) 0 = _ at e1
  have e2 : pairingFourierDual ν α (pairingFourier μ α ((L : Set X).indicator fun _ => (1 : ℂ))) =
      fun x => (pairingFourierConstant μ ν α : ℂ) * ((L : Set X).indicator fun _ => (1 : ℂ)) (-x) :=
    funext fun x => pairingFourierDual_pairingFourier_eq h μ ν hφ x
  rw [e2, pairingFourier_const_mul, pairingFourier_comp_neg h μ, neg_zero,
    pairingFourier_indicator μ h L hLo, Set.indicator_of_mem (h.annihilator _).zero_mem] at e1
  have hpos : (μ.real (L : Set X) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, measureReal_def]
    exact ENNReal.toReal_ne_zero.mpr ⟨(hLo.measure_pos μ ⟨0, L.zero_mem⟩).ne',
      hLc.measure_lt_top.ne⟩
  exact_mod_cast (mul_right_cancel₀ hpos e1).symm

private theorem integral_pairingFourier_mul_conj (h : IsPerfectBicharacter α) (μ : Measure X)
    [μ.IsAddHaarMeasure] (ν : Measure Y) [ν.IsAddHaarMeasure] {φ : X → ℂ}
    (hφ : φ ∈ schwartzBruhatSubmodule X) :
    ∫ y, pairingFourier μ α φ y * starRingEnd ℂ (pairingFourier μ α φ y) ∂ν =
      (pairingFourierConstant μ ν α : ℂ) * ∫ x, φ x * starRingEnd ℂ (φ x) ∂μ := by
  set Φ := pairingFourier μ α φ with hΦdef
  have hΦ : Φ ∈ schwartzBruhatSubmodule Y := pairingFourier_mem μ h hφ
  have hint : Integrable (Function.uncurry fun y x => α x y * φ x * starRingEnd ℂ (Φ y))
      (ν.prod μ) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact ((h.continuous.comp continuous_swap).mul (hφ.1.continuous.comp continuous_snd)).mul
        ((Complex.continuous_conj.comp hΦ.1.continuous).comp continuous_fst)
    · apply HasCompactSupport.intro (hΦ.2.isCompact.prod hφ.2.isCompact)
      rintro ⟨y, x⟩ hyx
      simp only [Set.mem_prod, not_and_or] at hyx
      rcases hyx with h' | h'
      · simp [image_eq_zero_of_notMem_tsupport h']
      · simp [image_eq_zero_of_notMem_tsupport h']
  have hinner : ∀ x, ∫ y, α x y * starRingEnd ℂ (Φ y) ∂ν =
      (pairingFourierConstant μ ν α : ℂ) * starRingEnd ℂ (φ x) := by
    intro x
    have h1 : ∀ y, α x y * starRingEnd ℂ (Φ y) = starRingEnd ℂ (α (-x) y * Φ y) := by
      intro y
      rw [map_mul, h.conj_apply, neg_neg]
    simp_rw [h1]
    rw [integral_conj]
    have h2 := pairingFourierDual_pairingFourier_eq h μ ν hφ (-x)
    rw [neg_neg] at h2
    change starRingEnd ℂ (pairingFourierDual ν α Φ (-x)) = _
    rw [h2, map_mul, Complex.conj_ofReal]
  calc ∫ y, Φ y * starRingEnd ℂ (Φ y) ∂ν
      = ∫ y, ∫ x, α x y * φ x * starRingEnd ℂ (Φ y) ∂μ ∂ν := by
        congr 1; ext y
        rw [integral_mul_const]
        rfl
    _ = ∫ x, ∫ y, α x y * φ x * starRingEnd ℂ (Φ y) ∂ν ∂μ := integral_integral_swap hint
    _ = ∫ x, φ x * ∫ y, α x y * starRingEnd ℂ (Φ y) ∂ν ∂μ := by
        congr 1; ext x
        rw [← integral_const_mul]
        congr 1; ext y; ring
    _ = (pairingFourierConstant μ ν α : ℂ) * ∫ x, φ x * starRingEnd ℂ (φ x) ∂μ := by
        simp_rw [hinner]
        rw [← integral_const_mul]
        congr 1; ext x; ring

omit [AddCommGroup X] [IsTopologicalAddGroup X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [CompactOpenExhaustion X] [AddCommGroup Y] [TopologicalSpace Y]
  [IsTopologicalAddGroup Y] [LocallyCompactSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y]
  [BorelSpace Y] [CompactOpenExhaustion Y] in
private theorem lintegral_enorm_sq_eq (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {f : X → ℂ}
    (hf : f ∈ schwartzBruhatSubmodule X) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ x, ‖f x‖ ^ 2 ∂μ) := by
  have h1 : Continuous f := hf.1.continuous
  have h3 : HasCompactSupport (fun x => ‖f x‖ ^ 2) := by
    have := hf.2.norm
    exact this.mul_right (f' := fun x => ‖f x‖) |>.mono (fun x hx => by simpa [sq] using hx)
  have hi : Integrable (fun x => ‖f x‖ ^ 2) μ :=
    (h1.norm.pow 2).integrable_of_hasCompactSupport h3
  rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun x => by positivity)]
  congr 1; ext x
  rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]

omit [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [BorelSpace X] [CompactOpenExhaustion X] [AddCommGroup Y]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [LocallyCompactSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] [CompactOpenExhaustion Y] in
private theorem integral_mul_conj_eq (μ : Measure X) (f : X → ℂ) :
    ∫ x, f x * starRingEnd ℂ (f x) ∂μ = ((∫ x, ‖f x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  congr 1; ext x
  rw [Complex.mul_conj']
  push_cast; rfl

/-- **Plancherel's formula for a perfect pairing** (GKT Theorem 1.37 (b) up to the normalization of
the measures): `∫ |ℱ_μ φ|² dν = C(μ, ν) ∫ |φ|² dμ`. -/
theorem lintegral_enorm_pairingFourier_sq (h : IsPerfectBicharacter α) (μ : Measure X)
    [μ.IsAddHaarMeasure] (ν : Measure Y) [ν.IsAddHaarMeasure] {φ : X → ℂ}
    (hφ : φ ∈ schwartzBruhatSubmodule X) :
    ∫⁻ y, ‖pairingFourier μ α φ y‖ₑ ^ 2 ∂ν =
      ENNReal.ofReal (pairingFourierConstant μ ν α) * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  have hC := pairingFourierConstant_pos μ ν α
  have hk := integral_pairingFourier_mul_conj h μ ν hφ
  rw [integral_mul_conj_eq, integral_mul_conj_eq] at hk
  have hk' : ∫ y, ‖pairingFourier μ α φ y‖ ^ 2 ∂ν =
      pairingFourierConstant μ ν α * ∫ x, ‖φ x‖ ^ 2 ∂μ := by exact_mod_cast hk
  rw [lintegral_enorm_sq_eq ν (pairingFourier_mem μ h hφ), lintegral_enorm_sq_eq μ hφ, hk',
    ENNReal.ofReal_mul hC.le]

/-- `C(μ, ν)` is also the constant of the flipped pairing with the measures exchanged. -/
theorem pairingFourierConstant_flip (h : IsPerfectBicharacter α) (μ : Measure X)
    [μ.IsAddHaarMeasure] (ν : Measure Y) [ν.IsAddHaarMeasure] :
    pairingFourierConstant ν μ (fun y x => α x y) = pairingFourierConstant μ ν α :=
  pairingFourierConstant_eq (pairingFourierConstant_pos μ ν α) fun _ hf y =>
    pairingFourier_pairingFourierDual_eq h μ ν hf y

/-- **Plancherel's formula for the dual transform** (GKT Theorem 1.37 (c) up to the normalization
of the measures): `∫ |ℱ'_ν f|² dμ = C(μ, ν) ∫ |f|² dν`. -/
theorem lintegral_enorm_pairingFourierDual_sq (h : IsPerfectBicharacter α) (μ : Measure X)
    [μ.IsAddHaarMeasure] (ν : Measure Y) [ν.IsAddHaarMeasure] {f : Y → ℂ}
    (hf : f ∈ schwartzBruhatSubmodule Y) :
    ∫⁻ x, ‖pairingFourierDual ν α f x‖ₑ ^ 2 ∂μ =
      ENNReal.ofReal (pairingFourierConstant μ ν α) * ∫⁻ y, ‖f y‖ₑ ^ 2 ∂ν := by
  rw [← pairingFourierConstant_flip h μ ν]
  exact lintegral_enorm_pairingFourier_sq h.flip ν μ hf

/-- `C(μ, rν) = r C(μ, ν)`. -/
theorem pairingFourierConstant_smul_right (h : IsPerfectBicharacter α) (μ : Measure X)
    [μ.IsAddHaarMeasure] (ν : Measure Y) [ν.IsAddHaarMeasure] {r : ℝ≥0} (hr : r ≠ 0) :
    pairingFourierConstant μ (r • ν) α = r * pairingFourierConstant μ ν α := by
  have hr' : (0 : ℝ) < r := lt_of_le_of_ne r.2 (by exact_mod_cast hr.symm)
  refine pairingFourierConstant_eq (by have := pairingFourierConstant_pos μ ν α; positivity)
    fun φ hφ x => ?_
  rw [pairingFourierDual, pairingFourier_smul_measure, ← pairingFourierDual,
    pairingFourierDual_pairingFourier_eq h μ ν hφ x]
  push_cast
  ring

/-- `C(rμ, ν) = r C(μ, ν)`. -/
theorem pairingFourierConstant_smul_left (h : IsPerfectBicharacter α) (μ : Measure X)
    [μ.IsAddHaarMeasure] (ν : Measure Y) [ν.IsAddHaarMeasure] {r : ℝ≥0} (hr : r ≠ 0) :
    pairingFourierConstant (r • μ) ν α = r * pairingFourierConstant μ ν α := by
  have : (r • μ).IsAddHaarMeasure := Measure.IsAddHaarMeasure.nnreal_smul μ hr
  rw [← pairingFourierConstant_flip h, ← pairingFourierConstant_flip h μ,
    pairingFourierConstant_smul_right h.flip ν μ hr]

/-! ### The dual measure -/

/-- **The dual measure** is `C(μ, ν)⁻¹ ν` for every Haar measure `ν` on `Y` (GKT Theorem 1.37 (b):
it exists and is unique). -/
theorem pairingDualMeasure_eq_smul (h : IsPerfectBicharacter α) (μ : Measure X)
    [μ.IsAddHaarMeasure] (ν : Measure Y) [ν.IsAddHaarMeasure] :
    pairingDualMeasure μ α = (pairingFourierConstant μ ν α)⁻¹.toNNReal • ν := by
  classical
  have hC := pairingFourierConstant_pos μ ν α
  have hr : (pairingFourierConstant μ ν α)⁻¹.toNNReal ≠ 0 := by
    simpa [Real.toNNReal_eq_zero] using hC
  set ν' := (pairingFourierConstant μ ν α)⁻¹.toNNReal • ν with hν'
  have : ν'.IsAddHaarMeasure := Measure.IsAddHaarMeasure.nnreal_smul ν hr
  have hν'1 : pairingFourierConstant μ ν' α = 1 := by
    rw [hν', pairingFourierConstant_smul_right h μ ν hr, Real.coe_toNNReal _ (inv_nonneg.2 hC.le),
      inv_mul_cancel₀ hC.ne']
  have hex : ∃ ν : Measure Y, ν.IsAddHaarMeasure ∧ ∀ φ ∈ schwartzBruhatSubmodule X, ∀ x,
      pairingFourierDual ν α (pairingFourier μ α φ) x = φ (-x) :=
    ⟨ν', this, fun φ hφ x => by
      rw [pairingFourierDual_pairingFourier_eq h μ ν' hφ x, hν'1, Complex.ofReal_one, one_mul]⟩
  rw [pairingDualMeasure, dite_eq_left_of_eq_true (eq_true hex)]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  have h3 : pairingFourierConstant μ hex.choose α = 1 :=
    pairingFourierConstant_eq one_pos fun φ hφ x => by
      rw [h2 φ hφ x, Complex.ofReal_one, one_mul]
  -- two Haar measures with constant `1` are equal
  have hs : hex.choose = Measure.addHaarScalarFactor hex.choose ν' • ν' :=
    Measure.isAddLeftInvariant_eq_smul _ _
  set s := Measure.addHaarScalarFactor hex.choose ν'
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hs
    exact (isOpen_univ.measure_pos hex.choose Set.univ_nonempty).ne' (by rw [hs]; rfl)
  have h4 := pairingFourierConstant_smul_right h μ ν' hs0
  rw [← hs, h3, hν'1, mul_one] at h4
  rw [hs, show s = 1 from NNReal.eq (by exact_mod_cast h4.symm), one_smul]

/-- The dual measure is a Haar measure. -/
theorem isAddHaarMeasure_pairingDualMeasure (h : IsPerfectBicharacter α) (μ : Measure X)
    [μ.IsAddHaarMeasure] : (pairingDualMeasure μ α).IsAddHaarMeasure := by
  rw [pairingDualMeasure_eq_smul h μ (Measure.addHaar : Measure Y)]
  exact Measure.IsAddHaarMeasure.nnreal_smul _
    (by simpa [Real.toNNReal_eq_zero] using pairingFourierConstant_pos μ Measure.addHaar α)

/-- The constant of `μ` and its dual measure is `1`. -/
theorem pairingFourierConstant_pairingDualMeasure (h : IsPerfectBicharacter α) (μ : Measure X)
    [μ.IsAddHaarMeasure] : pairingFourierConstant μ (pairingDualMeasure μ α) α = 1 := by
  have hC := pairingFourierConstant_pos μ (Measure.addHaar : Measure Y) α
  have hr : (pairingFourierConstant μ (Measure.addHaar : Measure Y) α)⁻¹.toNNReal ≠ 0 := by
    simpa [Real.toNNReal_eq_zero] using hC
  rw [pairingDualMeasure_eq_smul h μ Measure.addHaar, pairingFourierConstant_smul_right h μ _ hr,
    Real.coe_toNNReal _ (inv_nonneg.2 hC.le), inv_mul_cancel₀ hC.ne']

/-- **Fourier inversion for dual measures** (GKT Theorem 1.37 (d)): `ℱ'_{μ'} ℱ_μ φ = φ(-·)` and
`ℱ_μ ℱ'_{μ'} f = f(-·)` for `μ' = pairingDualMeasure μ α`. -/
theorem pairingFourierDual_pairingDualMeasure_pairingFourier (h : IsPerfectBicharacter α)
    (μ : Measure X) [μ.IsAddHaarMeasure] {φ : X → ℂ} (hφ : φ ∈ schwartzBruhatSubmodule X)
    (x : X) :
    pairingFourierDual (pairingDualMeasure μ α) α (pairingFourier μ α φ) x = φ (-x) := by
  have := isAddHaarMeasure_pairingDualMeasure h μ
  rw [pairingFourierDual_pairingFourier_eq h μ _ hφ x, pairingFourierConstant_pairingDualMeasure h,
    Complex.ofReal_one, one_mul]

theorem pairingFourier_pairingFourierDual_pairingDualMeasure (h : IsPerfectBicharacter α)
    (μ : Measure X) [μ.IsAddHaarMeasure] {f : Y → ℂ} (hf : f ∈ schwartzBruhatSubmodule Y)
    (y : Y) :
    pairingFourier μ α (pairingFourierDual (pairingDualMeasure μ α) α f) y = f (-y) := by
  have := isAddHaarMeasure_pairingDualMeasure h μ
  rw [pairingFourier_pairingFourierDual_eq h μ _ hf y, pairingFourierConstant_pairingDualMeasure h,
    Complex.ofReal_one, one_mul]

/-- **For dual measures the Fourier transforms are isometries** (GKT Theorem 1.37 (b), (c)). -/
theorem lintegral_enorm_pairingFourier_sq_pairingDualMeasure (h : IsPerfectBicharacter α)
    (μ : Measure X) [μ.IsAddHaarMeasure] {φ : X → ℂ} (hφ : φ ∈ schwartzBruhatSubmodule X) :
    ∫⁻ y, ‖pairingFourier μ α φ y‖ₑ ^ 2 ∂(pairingDualMeasure μ α) = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  have := isAddHaarMeasure_pairingDualMeasure h μ
  rw [lintegral_enorm_pairingFourier_sq h μ _ hφ, pairingFourierConstant_pairingDualMeasure h,
    ENNReal.ofReal_one, one_mul]

theorem lintegral_enorm_pairingFourierDual_sq_pairingDualMeasure (h : IsPerfectBicharacter α)
    (μ : Measure X) [μ.IsAddHaarMeasure] {f : Y → ℂ} (hf : f ∈ schwartzBruhatSubmodule Y) :
    ∫⁻ x, ‖pairingFourierDual (pairingDualMeasure μ α) α f x‖ₑ ^ 2 ∂μ =
      ∫⁻ y, ‖f y‖ₑ ^ 2 ∂(pairingDualMeasure μ α) := by
  have := isAddHaarMeasure_pairingDualMeasure h μ
  rw [lintegral_enorm_pairingFourierDual_sq h μ _ hf, pairingFourierConstant_pairingDualMeasure h,
    ENNReal.ofReal_one, one_mul]

/-- **Uniqueness of the dual measure** (GKT Theorem 1.37 (b)). -/
theorem eq_pairingDualMeasure_iff (h : IsPerfectBicharacter α) (μ : Measure X)
    [μ.IsAddHaarMeasure] (ν : Measure Y) [ν.IsAddHaarMeasure] :
    (∀ φ ∈ schwartzBruhatSubmodule X, ∀ x,
      pairingFourierDual ν α (pairingFourier μ α φ) x = φ (-x)) ↔ ν = pairingDualMeasure μ α := by
  constructor
  · intro h'
    have h1 : pairingFourierConstant μ ν α = 1 :=
      pairingFourierConstant_eq one_pos fun φ hφ x => by
        rw [h' φ hφ x, Complex.ofReal_one, one_mul]
    rw [pairingDualMeasure_eq_smul h μ ν, h1, inv_one, Real.toNNReal_one, one_smul]
  · rintro rfl
    exact fun φ hφ x => pairingFourierDual_pairingDualMeasure_pairingFourier h μ hφ x

/-- The dual of `rμ` is `r⁻¹` times the dual of `μ` (GKT Remark 1.38). -/
theorem pairingDualMeasure_smul (h : IsPerfectBicharacter α) (μ : Measure X) [μ.IsAddHaarMeasure]
    {r : ℝ≥0} (hr : r ≠ 0) : pairingDualMeasure (r • μ) α = r⁻¹ • pairingDualMeasure μ α := by
  have : (r • μ).IsAddHaarMeasure := Measure.IsAddHaarMeasure.nnreal_smul μ hr
  have hr' : (0 : ℝ) < r := lt_of_le_of_ne r.2 (by exact_mod_cast hr.symm)
  have hC := pairingFourierConstant_pos μ (Measure.addHaar : Measure Y) α
  rw [pairingDualMeasure_eq_smul h _ Measure.addHaar,
    pairingDualMeasure_eq_smul h μ Measure.addHaar,
    pairingFourierConstant_smul_left h μ _ hr, smul_smul]
  congr 1
  apply NNReal.eq
  simp only [NNReal.coe_mul, NNReal.coe_inv]
  rw [Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ (by positivity)]
  field_simp

/-- **`μ` and its dual measure are dual to each other** (GKT Remark 1.38): the dual measure of
`pairingDualMeasure μ α` for the flipped pairing is `μ`. -/
theorem pairingDualMeasure_pairingDualMeasure (h : IsPerfectBicharacter α) (μ : Measure X)
    [μ.IsAddHaarMeasure] :
    pairingDualMeasure (pairingDualMeasure μ α) (fun y x => α x y) = μ := by
  have := isAddHaarMeasure_pairingDualMeasure h μ
  rw [pairingDualMeasure_eq_smul h.flip _ μ, pairingFourierConstant_flip h,
    pairingFourierConstant_pairingDualMeasure h, inv_one, Real.toNNReal_one, one_smul]

end Haar

/-! ### The self-dual case -/

section SelfDual

variable {X : Type*} [AddCommGroup X] [TopologicalSpace X] {e : X → X → ℂ}

/-- A self-dual bicharacter is a perfect pairing of `X` with itself. -/
theorem IsSelfDualBicharacter.isPerfectBicharacter (he : IsSelfDualBicharacter e) :
    IsPerfectBicharacter e where
  map_add_left := he.map_add_left
  map_add_right := he.map_add_right
  norm_eq_one := he.norm_eq_one
  isLocallyConstant := he.isLocallyConstant
  small_left := he.small
  big_left := he.big
  small_right U hU := by
    obtain ⟨K, hK, hKU⟩ := he.small U hU
    exact ⟨K, hK, fun x hx => hKU x fun y hy => by rw [he.symm]; exact hx y hy⟩
  big_right U hU := by
    obtain ⟨K, hK, hKU⟩ := he.big U hU
    exact ⟨K, hK, fun x hx => hKU x fun y hy => by rw [he.symm]; exact hx y hy⟩

omit [AddCommGroup X] [TopologicalSpace X] in
/-- For a symmetric bicharacter both transforms are `bicharacterFourier`. -/
theorem pairingFourier_eq_bicharacterFourier [MeasurableSpace X] (μ : Measure X)
    (hs : ∀ x y, e x y = e y x) (φ : X → ℂ) :
    pairingFourier μ e φ = bicharacterFourier μ e φ := by
  funext y
  simp only [pairingFourier, bicharacterFourier, hs _ y]

variable [IsTopologicalAddGroup X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] [CompactOpenExhaustion X]

/-- For a self-dual bicharacter the dual measure of `μ` is `bicharacterDualMeasure μ e`. -/
theorem pairingDualMeasure_eq_bicharacterDualMeasure (he : IsSelfDualBicharacter e)
    (μ : Measure X) [μ.IsAddHaarMeasure] :
    pairingDualMeasure μ e = bicharacterDualMeasure μ e := by
  have h := he.isPerfectBicharacter
  have : (bicharacterDualMeasure μ e).IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.nnreal_smul μ
      (by simpa [Real.toNNReal_eq_zero] using bicharacterFourierConstant_pos μ e)
  refine ((eq_pairingDualMeasure_iff h μ _).1 fun φ hφ x => ?_).symm
  have e1 : pairingFourierDual (bicharacterDualMeasure μ e) e (pairingFourier μ e φ) x =
      bicharacterFourier (bicharacterDualMeasure μ e) e (bicharacterFourier μ e φ) x := by
    rw [pairingFourierDual, pairingFourier_eq_bicharacterFourier μ he.symm,
      pairingFourier_eq_bicharacterFourier _ fun x y => he.symm y x]
    congr 1
    funext a b
    exact he.symm b a
  rw [e1]
  exact bicharacterFourier_bicharacterDualMeasure he μ hφ x

end SelfDual

/-! ### Vector spaces over a local field (GKT (1.12)) -/

section VectorSpace

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {X Y : Type*} [AddCommGroup X] [Module F X]
  [FiniteDimensional F X] [TopologicalSpace X] [IsModuleTopology F X] [AddCommGroup Y]
  [Module F Y] [FiniteDimensional F Y] [TopologicalSpace Y] [IsModuleTopology F Y]

/-- **`ψ ∘ ⟨,⟩` is a perfect pairing** (GKT (1.12), p. 45) for a non-trivial continuous unitary
character `ψ` of `F` and a non-degenerate bilinear pairing `⟨,⟩ : X × Y → F` of
finite-dimensional vector spaces with their module topologies. The proof doubles the pairing to
the symmetric form `((x, y), (x', y')) ↦ ⟨x, y'⟩ + ⟨x', y⟩` on `X × Y`. -/
theorem isPerfectBicharacter_of_nondegenerate {ψ : AddChar F ℂ} (hψ : Continuous ψ)
    (hn : ∀ t, ‖ψ t‖ = 1) (h1 : ψ ≠ 1) (β : X →ₗ[F] Y →ₗ[F] F)
    (hl : ∀ y, (∀ x, β x y = 0) → y = 0) (hr : ∀ x, (∀ y, β x y = 0) → x = 0) :
    IsPerfectBicharacter fun x y => ψ (β x y) := by
  -- the symmetric form `B` on `X × Y` and its self-dual bicharacter
  let B : (X × Y) →ₗ[F] (X × Y) →ₗ[F] F :=
    (β.compl₂ (LinearMap.snd F X Y)).comp (LinearMap.fst F X Y) +
      ((β.compl₂ (LinearMap.snd F X Y)).comp (LinearMap.fst F X Y)).flip
  have hB : ∀ p q : X × Y, B p q = β p.1 q.2 + β q.1 p.2 := fun p q => rfl
  have hBs : ∀ p q, B p q = B q p := fun p q => by rw [hB, hB, add_comm]
  have hBn : ∀ q, (∀ p, B p q = 0) → q = 0 := by
    intro q hq
    have hq1 : ∀ x, β x q.2 = 0 := fun x => by simpa [hB] using hq (x, 0)
    have hq2 : ∀ y, β q.1 y = 0 := fun y => by simpa [hB] using hq (0, y)
    exact Prod.ext (hr _ hq2) (hl _ hq1)
  have he := isSelfDualBicharacter_of_symm (V := X × Y) hψ hn h1 B hBs hBn
  have hα : ∀ x y, ψ (β x y) = ψ (B (x, 0) (0, y)) := fun x y => by simp [hB]
  have hα' : ∀ (p : X × Y) (y : Y), ψ (B p (0, y)) = ψ (β p.1 y) := fun p y => by simp [hB]
  have hα'' : ∀ (x : X) (p : X × Y), ψ (B (x, 0) p) = ψ (β x p.2) := fun x p => by simp [hB]
  refine ⟨fun x x' y => ?_, fun x y y' => ?_, fun x y => hn _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [map_add, LinearMap.add_apply, AddChar.map_add_eq_mul]
  · rw [map_add, AddChar.map_add_eq_mul]
  · exact (isLocallyConstant_of_continuous_addChar ψ hψ).comp_continuous
      (IsModuleTopology.continuous_bilinear_of_finite_left β)
  · -- small_left
    intro U hU
    obtain ⟨K, hK, hKU⟩ := he.small (Prod.snd ⁻¹' U) (continuous_snd.continuousAt.preimage_mem_nhds
      (by simpa using hU))
    refine ⟨Prod.fst '' K, hK.image continuous_fst, fun y hy => ?_⟩
    have := hKU (0, y) fun p hp => by rw [hα']; exact hy _ ⟨p, hp, rfl⟩
    exact this
  · -- big_left
    intro U hU
    obtain ⟨K, hK, hKU⟩ := he.big (Prod.fst ⁻¹' U) (continuous_fst.continuousAt.preimage_mem_nhds
      (by simpa using hU))
    refine ⟨Prod.snd '' K, hK.image continuous_snd, fun y hy => ⟨(0, y), hKU (0, y) ?_, rfl⟩⟩
    intro p hp
    rw [hα']
    exact hy _ hp
  · -- small_right
    intro U hU
    obtain ⟨K, hK, hKU⟩ := he.small (Prod.fst ⁻¹' U) (continuous_fst.continuousAt.preimage_mem_nhds
      (by simpa using hU))
    refine ⟨Prod.snd '' K, hK.image continuous_snd, fun x hx => ?_⟩
    have := hKU (x, 0) fun p hp => by rw [he.symm, hα'']; exact hx _ ⟨p, hp, rfl⟩
    exact this
  · -- big_right
    intro U hU
    obtain ⟨K, hK, hKU⟩ := he.big (Prod.snd ⁻¹' U) (continuous_snd.continuousAt.preimage_mem_nhds
      (by simpa using hU))
    refine ⟨Prod.fst '' K, hK.image continuous_fst, fun x hx => ⟨(x, 0), hKU (x, 0) ?_, rfl⟩⟩
    intro p hp
    rw [he.symm, hα'']
    exact hx _ hp

end VectorSpace

end Langlands.HarmonicAnalysis
