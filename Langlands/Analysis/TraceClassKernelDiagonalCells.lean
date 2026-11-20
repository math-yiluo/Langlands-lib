import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Integral.Average

/-!
# Cell averages along a refining sequence of finite partitions

Helper module for the proof of `TraceClassContinuousKernelDiagonalStatement`.
-/

noncomputable section

open MeasureTheory Filter Topology Function

namespace Langlands.Analysis.OperatorIdeals.KernelDiagonal

variable {X : Type*}

/-- The level-`m` code of `x`: which of the sets `B 0, …, B (m - 1)` contain `x`. -/
def cellCode (B : ℕ → Set X) (m : ℕ) (x : X) : Fin m → Prop := fun i => x ∈ B i

/-- The level-`m` cell of `x`: the points with the same level-`m` code as `x`. -/
def cell (B : ℕ → Set X) (m : ℕ) (x : X) : Set X := cellCode B m ⁻¹' {cellCode B m x}

/-- The σ-algebra of unions of level-`m` cells. -/
abbrev cellSigma (B : ℕ → Set X) (m : ℕ) : MeasurableSpace X :=
  MeasurableSpace.comap (cellCode B m) inferInstance

variable {B : ℕ → Set X}

variable [MeasurableSpace X]

lemma measurable_cellCode (hB : ∀ n, MeasurableSet (B n)) (m : ℕ) :
    Measurable (cellCode B m) := by
  refine measurable_pi_iff.2 fun i => ?_
  exact measurableSet_setOfPred.1 (hB i)

lemma measurableSet_cell (hB : ∀ n, MeasurableSet (B n)) (m : ℕ) (x : X) :
    MeasurableSet (cell B m x) :=
  measurable_cellCode hB m (measurableSet_singleton _)

omit [MeasurableSpace X] in
lemma cell_subset {n m : ℕ} (h : n < m) {x : X} (hx : x ∈ B n) : cell B m x ⊆ B n := by
  intro y hy
  have := congrFun hy ⟨n, h⟩
  exact Eq.mpr this hx

lemma ae_measure_cell_ne_zero (ν : Measure X) :
    ∀ᵐ x ∂ν, ∀ m, ν (cell B m x) ≠ 0 := by
  rw [ae_all_iff]
  intro m
  rw [ae_iff]
  simp only [not_not]
  have : {x | ν (cell B m x) = 0} =
      cellCode B m ⁻¹' {c | ν (cellCode B m ⁻¹' {c}) = 0} := rfl
  rw [this, measure_preimage_eq_zero_iff_of_countable (Set.to_countable _)]
  exact fun c hc => hc

omit [MeasurableSpace X] in
lemma cellSigma_mono : Monotone (cellSigma B) := by
  intro m n hmn
  have : cellCode B m =
      (fun c : Fin n → Prop => fun i : Fin m => c (Fin.castLE hmn i)) ∘ cellCode B n := rfl
  rw [cellSigma, cellSigma, this, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono Measurable.of_discrete.comap_le

lemma cellSigma_le (hB : ∀ n, MeasurableSet (B n)) (m : ℕ) :
    cellSigma B m ≤ ‹MeasurableSpace X› :=
  (measurable_cellCode hB m).comap_le

/-- The filtration of the cell σ-algebras. -/
def cellFiltration (hB : ∀ n, MeasurableSet (B n)) : Filtration ℕ ‹MeasurableSpace X› :=
  ⟨cellSigma B, cellSigma_mono, cellSigma_le hB⟩

lemma le_iSup_cellSigma [TopologicalSpace X] [BorelSpace X]
    (hBn : ∀ x, ∀ U ∈ 𝓝 x, ∃ n, x ∈ B n ∧ B n ⊆ U) :
    ‹MeasurableSpace X› ≤ ⨆ m, cellSigma B m := by
  have hBm : ∀ n, MeasurableSet[⨆ m, cellSigma B m] (B n) := by
    intro n
    have : MeasurableSet[cellSigma B (n + 1)] (B n) :=
      ⟨{c | c ⟨n, Nat.lt_succ_self n⟩}, MeasurableSet.of_discrete, rfl⟩
    exact le_iSup (cellSigma B) (n + 1) _ this
  rw [BorelSpace.measurable_eq (α := X), borel]
  refine MeasurableSpace.generateFrom_le fun U hU => ?_
  have : U = ⋃ n ∈ {n | B n ⊆ U}, B n := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hxn, hnU⟩ := hBn x U (hU.mem_nhds hx)
      exact Set.mem_biUnion hnU hxn
    · intro hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨n, hn, hxn⟩ := hx
      exact hn hxn
  rw [this]
  exact MeasurableSet.biUnion (Set.to_countable _) fun n _ => hBm n

lemma setAverage_cell_ae_eq_condExp (ν : Measure X) [IsFiniteMeasure ν]
    (hB : ∀ n, MeasurableSet (B n)) (m : ℕ) {f : X → ℝ} (hf : Integrable f ν) :
    (fun x => ⨍ y in cell B m x, f y ∂ν) =ᵐ[ν] ν[f | cellSigma B m] := by
  set G : (Fin m → Prop) → ℝ := fun c => ⨍ y in cellCode B m ⁻¹' {c}, f y ∂ν with hG
  have hfun : (fun x => ⨍ y in cell B m x, f y ∂ν) = G ∘ cellCode B m := rfl
  have hsm : StronglyMeasurable[cellSigma B m] (G ∘ cellCode B m) :=
    (Measurable.of_discrete.comp (comap_measurable _)).stronglyMeasurable
  obtain ⟨C, hC⟩ : ∃ C, ∀ c, ‖G c‖ ≤ C := by
    obtain ⟨C, hC⟩ := (Set.finite_range fun c => ‖G c‖).bddAbove
    exact ⟨C, fun c => hC ⟨c, rfl⟩⟩
  have hint : Integrable (G ∘ cellCode B m) ν :=
    Integrable.of_bound (hsm.mono (cellSigma_le hB m)).aestronglyMeasurable C
      (Eventually.of_forall fun x => hC _)
  have hmeas : ∀ c, MeasurableSet (cellCode B m ⁻¹' {c}) :=
    fun c => measurable_cellCode hB m (measurableSet_singleton c)
  have hdisj : ∀ t : Finset (Fin m → Prop),
      Set.Pairwise (↑t) (Disjoint on fun c => cellCode B m ⁻¹' {c}) := by
    intro t c _ d _ hcd
    exact Disjoint.preimage _ (Set.disjoint_singleton.2 hcd)
  rw [hfun]
  refine ae_eq_condExp_of_forall_setIntegral_eq (cellSigma_le hB m) hf
    (fun s _ _ => hint.integrableOn) ?_ hsm.aestronglyMeasurable
  intro s hs _
  obtain ⟨S, -, rfl⟩ := hs
  have hU : cellCode B m ⁻¹' S = ⋃ c ∈ S.toFinite.toFinset, cellCode B m ⁻¹' {c} := by
    ext x
    simp
  rw [hU, integral_biUnion_finset _ (fun c _ => hmeas c) (hdisj _) (fun c _ => hint.integrableOn),
    integral_biUnion_finset _ (fun c _ => hmeas c) (hdisj _) (fun c _ => hf.integrableOn)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [setIntegral_congr_fun (hmeas c) (g := fun _ => G c) (fun x hx => by
    simp only [Function.comp_apply]
    rw [show cellCode B m x = c from hx]), setIntegral_const,
    measure_smul_setAverage f (measure_ne_top ν _)]

/-- **Lévy upward theorem for cell averages.** -/
theorem ae_tendsto_setAverage_cell [TopologicalSpace X] [BorelSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (hB : ∀ n, MeasurableSet (B n))
    (hBn : ∀ x, ∀ U ∈ 𝓝 x, ∃ n, x ∈ B n ∧ B n ⊆ U) {f : X → ℝ} (hf : Integrable f ν) :
    ∀ᵐ x ∂ν, Tendsto (fun m => ⨍ y in cell B m x, f y ∂ν) atTop (𝓝 (f x)) := by
  set f' := hf.aestronglyMeasurable.mk f
  have hf'i : Integrable f' ν := hf.congr hf.aestronglyMeasurable.ae_eq_mk
  have hf'm : StronglyMeasurable[⨆ n, cellFiltration hB n] f' :=
    hf.aestronglyMeasurable.stronglyMeasurable_mk.mono (le_iSup_cellSigma hBn)
  have h1 := hf'i.tendsto_ae_condExp hf'm
  have h2 : ∀ᵐ x ∂ν, ∀ m, ⨍ y in cell B m x, f' y ∂ν = ν[f' | cellSigma B m] x :=
    ae_all_iff.2 fun m => setAverage_cell_ae_eq_condExp ν hB m hf'i
  have h3 : ∀ m x, ⨍ y in cell B m x, f' y ∂ν = ⨍ y in cell B m x, f y ∂ν := fun m x => by
    rw [setAverage_eq, setAverage_eq,
      integral_congr_ae (ae_restrict_of_ae hf.aestronglyMeasurable.ae_eq_mk.symm)]
  filter_upwards [h1, h2, hf.aestronglyMeasurable.ae_eq_mk] with x hx1 hx2 hx3
  rw [hx3]
  have : (fun m => ⨍ y in cell B m x, f y ∂ν) = fun m => ν[f' | cellSigma B m] x := by
    funext m
    rw [← h3, hx2]
  rw [this]
  exact hx1

/-- The complex-valued version of `ae_tendsto_setAverage_cell`. -/
theorem ae_tendsto_setAverage_cell_complex [TopologicalSpace X] [BorelSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (hB : ∀ n, MeasurableSet (B n))
    (hBn : ∀ x, ∀ U ∈ 𝓝 x, ∃ n, x ∈ B n ∧ B n ⊆ U) {f : X → ℂ} (hf : Integrable f ν) :
    ∀ᵐ x ∂ν, Tendsto (fun m => ⨍ y in cell B m x, f y ∂ν) atTop (𝓝 (f x)) := by
  filter_upwards [ae_tendsto_setAverage_cell ν hB hBn hf.re,
    ae_tendsto_setAverage_cell ν hB hBn hf.im] with x hre him
  have key : ∀ m, ⨍ y in cell B m x, f y ∂ν =
      ((⨍ y in cell B m x, (f y).re ∂ν : ℝ) : ℂ) +
        ((⨍ y in cell B m x, (f y).im ∂ν : ℝ) : ℂ) * Complex.I := by
    intro m
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
      rw [setAverage_eq, setAverage_eq, Complex.smul_re, smul_eq_mul]
      congr 1
      simpa only [RCLike.re_to_complex] using
        (integral_re (hf.integrableOn (s := cell B m x))).symm
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
        Complex.ofReal_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
      rw [setAverage_eq, setAverage_eq, Complex.smul_im, smul_eq_mul]
      congr 1
      simpa only [RCLike.im_to_complex] using
        (integral_im (hf.integrableOn (s := cell B m x))).symm
  simp_rw [key]
  have h := (Complex.continuous_ofReal.tendsto _).comp hre |>.add
    (((Complex.continuous_ofReal.tendsto _).comp him).mul_const Complex.I)
  simpa only [Function.comp_apply, RCLike.re_to_complex, RCLike.im_to_complex,
    Complex.re_add_im] using h

end Langlands.Analysis.OperatorIdeals.KernelDiagonal
