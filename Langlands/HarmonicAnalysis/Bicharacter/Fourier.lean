import Langlands.HarmonicAnalysis.Bicharacter.SelfDual
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# The Fourier transform of a self-dual bicharacter

Let `X` be a commutative, Hausdorff, locally compact, second countable topological group with
arbitrarily large and small compact open subgroups (`CompactOpenExhaustion`), `μ` a Haar measure
on `X`, and `e` a self-dual bicharacter on `X` (`IsSelfDualBicharacter`). The Fourier transform

`bicharacterFourier μ e φ x = ∫ y, e x y * φ y ∂μ`

preserves the Schwartz–Bruhat functions (`bicharacterFourier_mem`), and applied twice it is a
positive multiple of the reflection `φ ↦ φ ∘ (-·)`:

`∃ C > 0, ∀ φ, ℱ (ℱ φ) x = C φ (-x)`  (`exists_pos_bicharacterFourier_bicharacterFourier`);

`C = 1` exactly when `μ` is the measure self-dual for `e`. With this constant, Plancherel's
formula `∫ |ℱ φ|² = C ∫ |φ|²` holds (`lintegral_enorm_bicharacterFourier_sq`).

The constant is computed on the indicator of a compact open subgroup `L`: its transform is
`μ(L)` times the indicator of the annihilator `L^⊥`, which is again compact open, and
`L^⊥⊥ = L`; so `C = μ(L) μ(L^⊥)`, and the same constant serves every function invariant under a
compact open subgroup, that is every Schwartz–Bruhat function. A. Weil, *Sur certains groupes
d'opérateurs unitaires*, Acta Math. 111 (1964), chapter I, n° 2, p. 147 (the Fourier transform
`Φ*(x*) = ∫ Φ(x) ⟨x, x*⟩ dx`, the dual Haar measure, the inversion formula and Plancherel's
formula) and n° 11, pp. 157–158 (the space `S(G)` of Bruhat, on which the Fourier transform induces
an automorphism).
-/

noncomputable section

open MeasureTheory
open scoped Topology

namespace Langlands.HarmonicAnalysis

variable {X : Type*} [AddCommGroup X] [TopologicalSpace X]

/-- The Fourier transform of a function on `X` for the bicharacter `e` and the measure `μ`:
`x ↦ ∫ y, e x y * φ y ∂μ`. -/
def bicharacterFourier [MeasurableSpace X] (μ : Measure X) (e : X → X → ℂ) (φ : X → ℂ) :
    X → ℂ :=
  fun x => ∫ y, e x y * φ y ∂μ

omit [AddCommGroup X] [TopologicalSpace X] in
theorem bicharacterFourier_apply [MeasurableSpace X] (μ : Measure X) (e : X → X → ℂ)
    (φ : X → ℂ) (x : X) : bicharacterFourier μ e φ x = ∫ y, e x y * φ y ∂μ := rfl

namespace BicharacterFourier.Internal

theorem _root_.Langlands.HarmonicAnalysis.eventually_add_eq_of_mem_schwartzBruhatSubmodule
    [IsTopologicalAddGroup X] {f : X → ℂ}
    (hf : f ∈ schwartzBruhatSubmodule X) : ∀ᶠ t in 𝓝 (0 : X), ∀ x, f (x + t) = f x := by
  have h1 : ∀ᶠ t in 𝓝 (0 : X), ∀ x ∈ tsupport f, f (x + t) = f x := by
    refine IsCompact.eventually_forall_of_forall_eventually hf.2 fun x _ => ?_
    have h2 : IsLocallyConstant fun q : X × X => (f (q.2 + q.1), f q.2) :=
      (hf.1.comp_continuous (by fun_prop)).prodMk (hf.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (0, x)] with q hq
    simp only [Prod.mk.injEq, add_zero] at hq
    rw [hq.1, hq.2]
  have h2 : ∀ᶠ t in 𝓝 (0 : X), ∀ x ∈ tsupport f, f (x + -t) = f x := by
    have h3 : Filter.Tendsto (fun t : X => -t) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg (G := X)).tendsto 0
    exact h3.eventually h1
  filter_upwards [h1, h2] with t ht ht' x
  by_cases hx : x ∈ tsupport f
  · exact ht x hx
  by_cases hx' : x + t ∈ tsupport f
  · rw [← ht' _ hx', add_neg_cancel_right]
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

end BicharacterFourier.Internal

open BicharacterFourier.Internal

variable [IsTopologicalAddGroup X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure] {e : X → X → ℂ}

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
/-- The Fourier transform of a self-dual bicharacter preserves the Schwartz–Bruhat functions. -/
theorem bicharacterFourier_mem (he : IsSelfDualBicharacter e) {φ : X → ℂ}
    (hφ : φ ∈ schwartzBruhatSubmodule X) :
    bicharacterFourier μ e φ ∈ schwartzBruhatSubmodule X := by
  obtain ⟨K, hK, hKm⟩ := he.big _ (eventually_add_eq_of_mem_schwartzBruhatSubmodule hφ)
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun y => ?_,
    HasCompactSupport.intro hK fun y hy => ?_⟩
  · have h1 : ∀ᶠ z in 𝓝 y, ∀ x ∈ tsupport φ, e z x = e y x := by
      refine IsCompact.eventually_forall_of_forall_eventually hφ.2 fun x _ => ?_
      have h2 : IsLocallyConstant fun q : X × X => (e q.1 q.2, e y q.2) :=
        he.isLocallyConstant.prodMk
          (he.isLocallyConstant.comp_continuous (continuous_const.prodMk continuous_snd))
      filter_upwards [h2.eventually_eq (y, x)] with q hq
      simp only [Prod.mk.injEq] at hq
      rw [hq.1, hq.2]
    filter_upwards [h1] with z hz
    unfold bicharacterFourier
    congr 1
    funext x
    by_cases hx : x ∈ tsupport φ
    · rw [hz x hx]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  · obtain ⟨t, ht, hne⟩ : ∃ t, (∀ x, φ (x + t) = φ x) ∧ e t y ≠ 1 := by
      by_contra hne
      exact hy (hKm y fun t ht => by
        by_contra h4
        exact hne ⟨t, ht, h4⟩)
    have h1 := integral_add_right_eq_self (μ := μ) (fun x => e y x * φ x) t
    have h2 : ∀ x, e y (x + t) * φ (x + t) = e t y * (e y x * φ x) := by
      intro x
      rw [ht, he.symm y (x + t), he.map_add_left, he.symm x y]; ring
    simp only [h2, integral_const_mul] at h1
    refine (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hne)
    unfold bicharacterFourier
    rw [sub_mul, h1, one_mul, sub_self]

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
/-- The Fourier transform as a linear endomorphism of the Schwartz–Bruhat space. -/
def bicharacterFourierSB (he : IsSelfDualBicharacter e) :
    SchwartzBruhat X →ₗ[ℂ] SchwartzBruhat X where
  toFun φ := ⟨bicharacterFourier μ e φ, bicharacterFourier_mem μ he φ.2⟩
  map_add' φ ψ := by
    apply Subtype.ext
    funext x
    change ∫ y, e x y * (φ y + ψ y) ∂μ = (∫ y, e x y * φ y ∂μ) + ∫ y, e x y * ψ y ∂μ
    simp_rw [mul_add]
    have hi : ∀ f : SchwartzBruhat X, Integrable (fun y => e x y * f y) μ := fun f =>
      ((he.continuous.comp (continuous_const.prodMk continuous_id)).mul
        (SchwartzBruhat.continuous f)).integrable_of_hasCompactSupport
          (SchwartzBruhat.hasCompactSupport f).mul_left
    exact integral_add (hi φ) (hi ψ)
  map_smul' c φ := by
    apply Subtype.ext
    funext x
    change ∫ y, e x y * (c * φ y) ∂μ = c * ∫ y, e x y * φ y ∂μ
    simp_rw [mul_left_comm (e x _) c]
    exact integral_const_mul c _

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
@[simp]
theorem coe_bicharacterFourierSB (he : IsSelfDualBicharacter e) (φ : SchwartzBruhat X) :
    (bicharacterFourierSB μ he φ : X → ℂ) = bicharacterFourier μ e φ := rfl

namespace BicharacterFourier.Internal

omit [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X]
  [BorelSpace X] in
theorem _root_.Langlands.HarmonicAnalysis.exists_nhds_add_eq_of_mem_schwartzBruhatSubmodule
    {f : X → ℂ} (hf : f ∈ schwartzBruhatSubmodule X) :
    ∃ U ∈ 𝓝 (0 : X), ∀ M : AddSubgroup X, (M : Set X) ⊆ U → ∀ t ∈ M, ∀ x,
      f (x + t) = f x := by
  have hf' : IsLocallyConstant f ∧ HasCompactSupport f := hf
  have hS : IsOpen {p : X × X | f (p.1 + p.2) - f p.1 = 0} :=
    ((hf'.1.comp_continuous continuous_add).comp₂ (hf'.1.comp_continuous continuous_fst)
      (fun a b : ℂ => a - b)).isOpen_fiber 0
  have hsub : tsupport f ×ˢ ({0} : Set X) ⊆ {p : X × X | f (p.1 + p.2) - f p.1 = 0} := by
    rintro ⟨x, t⟩ ⟨_, ht⟩
    simp only [Set.mem_singleton_iff] at ht
    subst ht
    simp
  obtain ⟨u, v, -, hv, hKu, h0v, huv⟩ :=
    generalized_tube_lemma hf'.2.isCompact isCompact_singleton hS hsub
  refine ⟨v, hv.mem_nhds (h0v (Set.mem_singleton 0)), fun M hM t ht x => ?_⟩
  have key : ∀ y ∈ tsupport f, ∀ s ∈ M, f (y + s) = f y := fun y hy s hs => by
    have h := huv (show (y, s) ∈ u ×ˢ v from ⟨hKu hy, hM hs⟩)
    exact sub_eq_zero.mp h
  by_cases hx : x ∈ tsupport f
  · exact key x hx t ht
  · by_cases hxt : x + t ∈ tsupport f
    · have h := key (x + t) hxt (-t) (M.neg_mem ht)
      rw [add_neg_cancel_right] at h
      exact h.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxt]

omit [TopologicalSpace X] [IsTopologicalAddGroup X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
theorem indicator_invariant (L : AddSubgroup X) (c : ℂ) :
    ∀ t ∈ L, ∀ x, (L : Set X).indicator (fun _ => c) (x + t) =
      (L : Set X).indicator (fun _ => c) x := by
  intro t ht x
  by_cases hx : x ∈ (L : Set X)
  · have hxt : x + t ∈ (L : Set X) := L.add_mem hx ht
    rw [Set.indicator_of_mem hxt, Set.indicator_of_mem hx]
  · have hxt : x + t ∉ (L : Set X) := fun h => hx (by simpa using L.sub_mem h ht)
    rw [Set.indicator_of_notMem hxt, Set.indicator_of_notMem hx]

omit [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X]
  [BorelSpace X] in
theorem _root_.Langlands.HarmonicAnalysis.indicator_one_mem_schwartzBruhatSubmodule
    (L : AddSubgroup X) (hc : IsCompact (L : Set X)) (ho : IsOpen (L : Set X)) :
    (L : Set X).indicator (fun _ => (1 : ℂ)) ∈ schwartzBruhatSubmodule X := by
  have hcl : IsClosed (L : Set X) := AddSubgroup.isClosed_of_isOpen L ho
  show IsLocallyConstant _ ∧ HasCompactSupport _
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro x
    by_cases hx : x ∈ (L : Set X)
    · exact ⟨(L : Set X), ho, hx, fun y hy => by
        rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
    · exact ⟨(L : Set X)ᶜ, hcl.isOpen_compl, hx, fun y hy => by
        rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩
  · exact HasCompactSupport.intro' hc hcl fun x hx => Set.indicator_of_notMem hx _

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
theorem bicharacterFourier_eq_zero (he : IsSelfDualBicharacter e) {M : Set X} {f : X → ℂ}
    (hs : ∀ t ∈ M, ∀ x, f (x + t) = f x) {y : X} (hy : y ∉ he.annihilator M) :
    bicharacterFourier μ e f y = 0 := by
  have hy' : ¬ ∀ t ∈ M, e t y = 1 := hy
  simp only [not_forall] at hy'
  obtain ⟨t, ht, hne⟩ := hy'
  have hne' : e y t ≠ 1 := by rwa [he.symm]
  have key : bicharacterFourier μ e f y = e y t * bicharacterFourier μ e f y := by
    simp only [bicharacterFourier]
    calc ∫ z, e y z * f z ∂μ = ∫ z, e y (t + z) * f (t + z) ∂μ :=
          (integral_add_left_eq_self (fun z => e y z * f z) t).symm
      _ = ∫ z, e y t * (e y z * f z) ∂μ := by
          congr 1; ext z
          rw [he.map_add_right, add_comm t z, hs t ht z]; ring
      _ = e y t * ∫ z, e y z * f z ∂μ := integral_const_mul _ _
  by_contra h
  exact hne' (mul_right_cancel₀ h (key.symm.trans (one_mul _).symm))

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
theorem bicharacterFourier_indicator (he : IsSelfDualBicharacter e) (L : AddSubgroup X)
    (ho : IsOpen (L : Set X)) (x : X) :
    bicharacterFourier μ e ((L : Set X).indicator fun _ => (1 : ℂ)) x =
      (he.annihilator L : Set X).indicator (fun _ => (μ.real (L : Set X) : ℂ)) x := by
  by_cases hx : x ∈ (he.annihilator L : Set X)
  · rw [Set.indicator_of_mem hx]
    have hx' : ∀ y ∈ (L : Set X), e y x = 1 := hx
    simp only [bicharacterFourier]
    have h : (fun z => e x z * (L : Set X).indicator (fun _ => (1 : ℂ)) z) =
        (L : Set X).indicator (fun _ => (1 : ℂ)) := by
      ext z
      by_cases hz : z ∈ (L : Set X)
      · rw [Set.indicator_of_mem hz, mul_one, he.symm, hx' z hz]
      · rw [Set.indicator_of_notMem hz, mul_zero]
    rw [h, integral_indicator_const _ ho.measurableSet]
    simp
  · rw [Set.indicator_of_notMem hx]
    exact bicharacterFourier_eq_zero μ he (indicator_invariant L 1) hx

theorem exists_bicharacterFourier_bicharacterFourier_of_annihilator_invariant
    (he : IsSelfDualBicharacter e) (L : AddSubgroup X)
    (hLc : IsCompact (L : Set X)) (hLo : IsOpen (L : Set X)) :
    ∃ C : ℝ, 0 < C ∧ ∀ φ ∈ schwartzBruhatSubmodule X,
      (∀ t ∈ he.annihilator (L : Set X), ∀ x, φ (x + t) = φ x) →
      ∀ x, bicharacterFourier μ e (bicharacterFourier μ e φ) x = (C : ℂ) * φ (-x) := by
  set A := he.annihilator (L : Set X) with hA
  set B := he.annihilator (A : Set X) with hB
  have hAo : IsOpen (A : Set X) := he.isOpen_annihilator hLc
  have hAc : IsCompact (A : Set X) := by
    obtain ⟨K, hK, hKA⟩ := he.big (L : Set X) (hLo.mem_nhds L.zero_mem)
    exact hK.of_isClosed_subset (AddSubgroup.isClosed_of_isOpen A hAo) fun y hy => hKA y hy
  have hBo : IsOpen (B : Set X) := he.isOpen_annihilator hAc
  have hBc : IsCompact (B : Set X) := by
    obtain ⟨K, hK, hKB⟩ := he.big (A : Set X) (hAo.mem_nhds A.zero_mem)
    exact hK.of_isClosed_subset (AddSubgroup.isClosed_of_isOpen B hBo) fun y hy => hKB y hy
  have hLB : (L : Set X) ⊆ B := by
    intro z hz y hy
    have hy' : ∀ x ∈ (L : Set X), e x y = 1 := hy
    rw [he.symm]
    exact hy' z hz
  have hBA : (he.annihilator (B : Set X) : Set X) = A := by
    ext z
    constructor
    · intro hz
      have hz' : ∀ y ∈ (B : Set X), e y z = 1 := hz
      exact fun x hx => hz' x (hLB hx)
    · intro hz y hy
      have hy' : ∀ w ∈ (A : Set X), e w y = 1 := hy
      rw [he.symm]
      exact hy' z hz
  have hApos : 0 < μ.real (A : Set X) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (hAo.measure_pos μ ⟨0, A.zero_mem⟩).ne' hAc.measure_lt_top.ne
  have hBpos : 0 < μ.real (B : Set X) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (hBo.measure_pos μ ⟨0, B.zero_mem⟩).ne' hBc.measure_lt_top.ne
  refine ⟨μ.real (A : Set X) * μ.real (B : Set X), mul_pos hApos hBpos, fun φ hφ hs w => ?_⟩
  have hφ' : IsLocallyConstant φ ∧ HasCompactSupport φ := hφ
  have hSc : IsCompact (tsupport φ) := hφ'.2.isCompact
  have : IsFiniteMeasure (μ.restrict (tsupport φ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hSc.measure_lt_top⟩
  have : IsFiniteMeasure (μ.restrict (B : Set X)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hBc.measure_lt_top⟩
  have h1 : ∀ x, ∫ z, e x z * φ z ∂μ = ∫ z in tsupport φ, e x z * φ z ∂μ := fun x =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
      rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]).symm
  have h2 : ∫ x, e w x * ∫ z, e x z * φ z ∂μ ∂μ =
      ∫ x in (B : Set X), e w x * ∫ z, e x z * φ z ∂μ ∂μ :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      have h0 := bicharacterFourier_eq_zero μ he hs (y := x) hx
      simp only [bicharacterFourier] at h0
      rw [h0, mul_zero]).symm
  have h3 : ∀ x, e w x * ∫ z in tsupport φ, e x z * φ z ∂μ =
      ∫ z in tsupport φ, e w x * (e x z * φ z) ∂μ := fun x => (integral_const_mul _ _).symm
  obtain ⟨C0, hC0⟩ := hφ'.1.continuous.bounded_above_of_compact_support hφ'.2
  have hcont : Continuous (Function.uncurry fun x z => e w x * (e x z * φ z)) :=
    (he.continuous.comp (continuous_const.prodMk continuous_fst)).mul
      (he.continuous.mul (hφ'.1.continuous.comp continuous_snd))
  have hint : Integrable (Function.uncurry fun x z => e w x * (e x z * φ z))
      ((μ.restrict (B : Set X)).prod (μ.restrict (tsupport φ))) :=
    (integrable_const C0).mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun p => by
      simp only [Function.uncurry, norm_mul, he.norm_eq_one, one_mul]
      exact hC0 p.2)
  have h4 : ∀ z, ∫ x in (B : Set X), e w x * (e x z * φ z) ∂μ =
      φ z * (he.annihilator (B : Set X) : Set X).indicator
        (fun _ => (μ.real (B : Set X) : ℂ)) (w + z) := by
    intro z
    have hB1 := bicharacterFourier_indicator μ he B hBo (w + z)
    simp only [bicharacterFourier] at hB1
    rw [← hB1, ← integral_indicator hBo.measurableSet, mul_comm (φ z), ← integral_mul_const]
    congr 1
    ext x
    by_cases hx : x ∈ (B : Set X)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, he.map_add_left, he.symm z x]
      ring
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      ring
  have h5 : ∀ z, φ z * (he.annihilator (B : Set X) : Set X).indicator
      (fun _ => (μ.real (B : Set X) : ℂ)) (w + z) =
      φ (-w) * (he.annihilator (B : Set X) : Set X).indicator
        (fun _ => (μ.real (B : Set X) : ℂ)) (w + z) := by
    intro z
    by_cases hz : w + z ∈ (he.annihilator (B : Set X) : Set X)
    · have hzA : w + z ∈ (A : Set X) := hBA.subset hz
      have h := hs (w + z) hzA (-w)
      rw [neg_add_cancel_left] at h
      rw [h]
    · rw [Set.indicator_of_notMem hz, mul_zero, mul_zero]
  have h6 : ∫ z in tsupport φ, φ (-w) * (he.annihilator (B : Set X) : Set X).indicator
      (fun _ => (μ.real (B : Set X) : ℂ)) (w + z) ∂μ =
      ∫ z, φ (-w) * (he.annihilator (B : Set X) : Set X).indicator
        (fun _ => (μ.real (B : Set X) : ℂ)) (w + z) ∂μ := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_
    rw [← h5 z, image_eq_zero_of_notMem_tsupport hz, zero_mul]
  have hAm : MeasurableSet (he.annihilator (B : Set X) : Set X) := by
    rw [hBA]
    exact hAo.measurableSet
  simp only [bicharacterFourier]
  rw [h2]
  simp_rw [h1, h3]
  rw [integral_integral_swap hint]
  simp_rw [h4, h5]
  rw [h6, integral_const_mul,
    integral_add_left_eq_self (fun z => (he.annihilator (B : Set X) : Set X).indicator
      (fun _ => (μ.real (B : Set X) : ℂ)) z) w,
    integral_indicator_const _ hAm, hBA, Complex.real_smul]
  push_cast
  ring

theorem exists_bicharacterFourier_bicharacterFourier_of_invariant [CompactOpenExhaustion X]
    (he : IsSelfDualBicharacter e) (M : AddSubgroup X) (hMo : IsOpen (M : Set X)) :
    ∃ C : ℝ, 0 < C ∧ ∀ φ ∈ schwartzBruhatSubmodule X, (∀ t ∈ M, ∀ x, φ (x + t) = φ x) →
      ∀ x, bicharacterFourier μ e (bicharacterFourier μ e φ) x = (C : ℂ) * φ (-x) := by
  obtain ⟨K, hK, hKM⟩ := he.small (M : Set X) (hMo.mem_nhds M.zero_mem)
  obtain ⟨L, hLc, hLo, hKL⟩ := CompactOpenExhaustion.exists_superset K hK
  obtain ⟨C, hC, hCφ⟩ :=
    exists_bicharacterFourier_bicharacterFourier_of_annihilator_invariant μ he L hLc hLo
  refine ⟨C, hC, fun φ hφ hs => hCφ φ hφ fun t ht => hs t (hKM t fun x hx => ?_)⟩
  exact (show ∀ y ∈ (L : Set X), e y t = 1 from ht) x (hKL hx)

end BicharacterFourier.Internal

/-- **Fourier inversion for a self-dual bicharacter.** Applied twice, the Fourier transform is a
positive multiple of the reflection on Schwartz–Bruhat functions. -/
theorem exists_pos_bicharacterFourier_bicharacterFourier [CompactOpenExhaustion X]
    (he : IsSelfDualBicharacter e) :
    ∃ C : ℝ, 0 < C ∧ ∀ φ ∈ schwartzBruhatSubmodule X, ∀ x,
      bicharacterFourier μ e (bicharacterFourier μ e φ) x = (C : ℂ) * φ (-x) := by
  obtain ⟨M0, hM0c, hM0o, -⟩ := CompactOpenExhaustion.exists_superset (∅ : Set X) isCompact_empty
  obtain ⟨C, hC, hCφ⟩ := exists_bicharacterFourier_bicharacterFourier_of_invariant μ he M0 hM0o
  refine ⟨C, hC, fun φ hφ x => ?_⟩
  obtain ⟨U, hU, hUinv⟩ := exists_nhds_add_eq_of_mem_schwartzBruhatSubmodule hφ
  obtain ⟨M1, -, hM1o, hM1U⟩ := CompactOpenExhaustion.exists_subset U hU
  have hMo : IsOpen ((M1 ⊓ M0 : AddSubgroup X) : Set X) := by
    rw [AddSubgroup.coe_inf]
    exact hM1o.inter hM0o
  obtain ⟨C', -, hC'φ⟩ := exists_bicharacterFourier_bicharacterFourier_of_invariant μ he
    (M1 ⊓ M0) hMo
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

/-! ### Plancherel -/

namespace BicharacterFourier.Internal

theorem integral_bicharacterFourier_mul_conj (he : IsSelfDualBicharacter e) (C : ℝ)
    (hinv : ∀ φ ∈ schwartzBruhatSubmodule X, ∀ x,
      bicharacterFourier μ e (bicharacterFourier μ e φ) x = (C : ℂ) * φ (-x))
    (φ : X → ℂ) (hφ : φ ∈ schwartzBruhatSubmodule X) :
    ∫ x, bicharacterFourier μ e φ x * starRingEnd ℂ (bicharacterFourier μ e φ x) ∂μ =
      (C : ℂ) * ∫ y, φ y * starRingEnd ℂ (φ y) ∂μ := by
  set Φ := bicharacterFourier μ e φ with hΦdef
  have hΦ : Φ ∈ schwartzBruhatSubmodule X := bicharacterFourier_mem μ he hφ
  have hint : Integrable (Function.uncurry fun x y => e x y * φ y * starRingEnd ℂ (Φ x))
      (μ.prod μ) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (he.continuous.mul (hφ.1.continuous.comp continuous_snd)).mul
        ((Complex.continuous_conj.comp hΦ.1.continuous).comp continuous_fst)
    · apply HasCompactSupport.intro (hΦ.2.isCompact.prod hφ.2.isCompact)
      rintro ⟨x, y⟩ hxy
      simp only [Set.mem_prod, not_and_or] at hxy
      rcases hxy with h | h
      · simp [image_eq_zero_of_notMem_tsupport h]
      · simp [image_eq_zero_of_notMem_tsupport h]
  have hinner : ∀ y, ∫ x, e x y * starRingEnd ℂ (Φ x) ∂μ = (C : ℂ) * starRingEnd ℂ (φ y) := by
    intro y
    have h1 : ∀ x, e x y * starRingEnd ℂ (Φ x) = starRingEnd ℂ (e (-y) x * Φ x) := by
      intro x
      rw [map_mul, he.conj_apply, neg_neg, he.symm]
    simp_rw [h1]
    rw [integral_conj]
    have h2 := hinv φ hφ (-y)
    rw [neg_neg] at h2
    change starRingEnd ℂ (bicharacterFourier μ e Φ (-y)) = _
    rw [h2, map_mul, Complex.conj_ofReal]
  calc ∫ x, Φ x * starRingEnd ℂ (Φ x) ∂μ
      = ∫ x, ∫ y, e x y * φ y * starRingEnd ℂ (Φ x) ∂μ ∂μ := by
        congr 1; ext x
        rw [integral_mul_const]
        rfl
    _ = ∫ y, ∫ x, e x y * φ y * starRingEnd ℂ (Φ x) ∂μ ∂μ := integral_integral_swap hint
    _ = ∫ y, φ y * ∫ x, e x y * starRingEnd ℂ (Φ x) ∂μ ∂μ := by
        congr 1; ext y
        rw [← integral_const_mul]
        congr 1; ext x; ring
    _ = (C : ℂ) * ∫ y, φ y * starRingEnd ℂ (φ y) ∂μ := by
        simp_rw [hinner]
        rw [← integral_const_mul]
        congr 1; ext y; ring

end BicharacterFourier.Internal

/-- **Plancherel's formula** for a self-dual bicharacter, with the constant of
`exists_pos_bicharacterFourier_bicharacterFourier`. -/
theorem lintegral_enorm_bicharacterFourier_sq (he : IsSelfDualBicharacter e) (C : ℝ) (hC : 0 < C)
    (hinv : ∀ φ ∈ schwartzBruhatSubmodule X, ∀ x,
      bicharacterFourier μ e (bicharacterFourier μ e φ) x = (C : ℂ) * φ (-x))
    {φ : X → ℂ} (hφ : φ ∈ schwartzBruhatSubmodule X) :
    ∫⁻ x, ‖bicharacterFourier μ e φ x‖ₑ ^ 2 ∂μ = ENNReal.ofReal C * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  have hΦ : bicharacterFourier μ e φ ∈ schwartzBruhatSubmodule X := bicharacterFourier_mem μ he hφ
  have hL : ∀ f ∈ schwartzBruhatSubmodule X,
      ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ x, ‖f x‖ ^ 2 ∂μ) := by
    intro f hf
    have h1 : Continuous f := hf.1.continuous
    have h2 : HasCompactSupport f := hf.2
    have h3 : HasCompactSupport (fun x => ‖f x‖ ^ 2) := by
      have := h2.norm
      exact this.mul_right (f' := fun x => ‖f x‖) |>.mono (fun x hx => by simpa [sq] using hx)
    have hi : Integrable (fun x => ‖f x‖ ^ 2) μ :=
      (h1.norm.pow 2).integrable_of_hasCompactSupport h3
    rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun x => by positivity)]
    congr 1; ext x
    rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  have hC' : ∀ f : X → ℂ, ∫ x, f x * starRingEnd ℂ (f x) ∂μ = ((∫ x, ‖f x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    intro f
    rw [← integral_complex_ofReal]
    congr 1; ext x
    rw [Complex.mul_conj']
    push_cast; rfl
  have hk := integral_bicharacterFourier_mul_conj μ he C hinv φ hφ
  rw [hC', hC'] at hk
  have hk' : ∫ x, ‖bicharacterFourier μ e φ x‖ ^ 2 ∂μ = C * ∫ x, ‖φ x‖ ^ 2 ∂μ := by
    exact_mod_cast hk
  rw [hL _ hΦ, hL _ hφ, hk', ENNReal.ofReal_mul hC.le]

end Langlands.HarmonicAnalysis
