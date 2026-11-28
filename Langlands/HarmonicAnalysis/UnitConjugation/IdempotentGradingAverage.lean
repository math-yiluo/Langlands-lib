import Langlands.HarmonicAnalysis.UnitConjugation.OrderLevels
import Langlands.HarmonicAnalysis.UnitConjugation.KernelFlagCommutator
import Langlands.HarmonicAnalysis.UnitConjugation.LatticeTests
import Langlands.HarmonicAnalysis.UnitConjugation.InvariantDistribution

/-!
# Decreasing averages of lattice coset tests near a graded nilpotent element

The geometric input of Howe's finiteness theorem (Harish-Chandra's condition `C(L)`, Theorem 13.1
of his notes) for an associative algebra: near a nilpotent `X₀` in a grading of `A` by orthogonal
idempotents of a compact open order `R`, the indicator of a coset `x + ϖ ^ s R` of a large
element `x` has, for every conjugation-invariant distribution, the same value as an
`ϖ ^ s R`-invariant test supported on smaller elements (`exists_decreasing_average`). The
ingredients are an averaging lemma over the finitely many cosets of one lattice in another
(`exists_conj_average`), the conjugation by the grading element `∑ ϖ ^ i e i`, and a single
Newton step for the unit `1 - ϖ ^ h y` (`exists_unit_conj_sub_mem`).
-/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open Set Function Finset ValuativeRel

section Averaging

variable {A : Type*} [Ring A] [TopologicalSpace A] [IsTopologicalRing A]
  (L : AddSubgroup A) (hLo : IsOpen (L : Set A)) (hLc : IsCompact (L : Set A))

theorem latticeCosetTest_apply_eq [DecidablePred (· ∈ L)] (y z : A) :
    latticeCosetTest L hLo hLc y z = if z - y ∈ L then 1 else 0 := by
  classical
  rw [latticeCosetTest_apply]
  have hiff : QuotientAddGroup.mk' L z = QuotientAddGroup.mk' L y ↔ z - y ∈ L := by
    rw [QuotientAddGroup.mk'_eq_mk']
    constructor
    · rintro ⟨c, hc, rfl⟩
      simpa using L.neg_mem hc
    · intro h
      exact ⟨y - z, by simpa using L.neg_mem h, by abel⟩
  by_cases h : z - y ∈ L
  · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (hiff.mp h')), ite_eq_right h]

include hLo in
private theorem quotient_isLocallyConstant' : IsLocallyConstant (QuotientAddGroup.mk' L) := by
  apply (IsLocallyConstant.iff_eventually_eq _).2
  intro x
  have ho : IsOpen (Homeomorph.addLeft x '' (L : Set A)) := (Homeomorph.addLeft x).isOpenMap _ hLo
  have hx : x ∈ Homeomorph.addLeft x '' (L : Set A) := ⟨0, L.zero_mem, by simp⟩
  filter_upwards [ho.mem_nhds hx] with y hy
  obtain ⟨t, ht, rfl⟩ := hy
  exact ((QuotientAddGroup.mk'_eq_mk' L).2 ⟨t, ht, rfl⟩).symm

/-- **Averaging over the cosets of `L` in `x + M`.** Let `L ≤ M` be additive subgroups, `L`
compact open and `M` compact, and let `γ` be a unit with `γ⁻¹ L γ ⊆ M`. If every invariant
distribution takes the same value on the indicators of all cosets `y + L ⊆ x + M`, then the
normalized indicator of `γ (x + M) γ⁻¹` is an `L`-invariant test on which every invariant
distribution takes its value at the indicator of `x + L`. -/
theorem exists_conj_average (M : AddSubgroup A) (hLM : L ≤ M) (hMc : IsCompact (M : Set A))
    (γ : Aˣ) (hγ : ∀ t ∈ L, ((γ⁻¹ : Aˣ) : A) * t * γ ∈ M) (x : A)
    (hcos : ∀ y, y - x ∈ M → ∀ T : Distribution A, IsConjugationInvariant T →
      T (latticeCosetTest L hLo hLc y) = T (latticeCosetTest L hLo hLc x)) :
    ∃ f : SchwartzBruhat A, f ∈ latticeInvariantTests L ∧
      (∀ z, f z ≠ 0 → ((γ⁻¹ : Aˣ) : A) * z * γ - x ∈ M) ∧
      ∀ T : Distribution A, IsConjugationInvariant T →
        T f = T (latticeCosetTest L hLo hLc x) := by
  classical
  -- the set `x + M`
  have hMo : IsOpen (M : Set A) := AddSubgroup.isOpen_mono hLM hLo
  let S : Set A := {z | z - x ∈ M}
  have hS : S = Homeomorph.addLeft x '' (M : Set A) := by
    ext z
    constructor
    · intro hz; exact ⟨z - x, hz, by simp⟩
    · rintro ⟨t, ht, rfl⟩; simpa [S] using ht
  have hSc : IsCompact S := by rw [hS]; exact hMc.image (Homeomorph.addLeft x).continuous
  have hSo : IsClopen S := by
    rw [hS]
    exact ⟨(Homeomorph.addLeft x).isClosedMap _ (M.isClosed_of_isOpen hMo),
      (Homeomorph.addLeft x).isOpenMap _ hMo⟩
  let g : SchwartzBruhat A := Hecke.TestFunction.characteristic hSo hSc
  -- the finitely many cosets of `L` in `M`
  let π := QuotientAddGroup.mk' L
  let Q := π '' (M : Set A)
  have hQ : Q.Finite := by
    let : TopologicalSpace (A ⧸ L) := ⊥
    have : DiscreteTopology (A ⧸ L) := ⟨rfl⟩
    exact (hMc.image (quotient_isLocallyConstant' L hLo).continuous).finite_of_discrete
  have hrep (q : Q) : ∃ y : A, y ∈ M ∧ π y = q.val := q.property
  choose r hrM hrπ using hrep
  let : Fintype Q := hQ.fintype
  -- decomposition of `g` into coset indicators
  have hdec : g = ∑ q : Q, latticeCosetTest L hLo hLc (x + r q) := by
    apply Hecke.TestFunction.ext
    intro z
    simp only [g, Hecke.TestFunction.characteristic_apply, Submodule.coe_sum, Finset.sum_apply,
      latticeCosetTest_apply_eq L hLo hLc]
    by_cases hz : z - x ∈ M
    · rw [indicator_of_mem (show z ∈ S from hz)]
      let q₀ : Q := ⟨π (z - x), ⟨z - x, hz, rfl⟩⟩
      rw [Finset.sum_eq_single q₀]
      · rw [ite_eq_left]
        have : π (r q₀) = π (z - x) := hrπ q₀
        rw [QuotientAddGroup.mk'_eq_mk'] at this
        obtain ⟨c, hc, hcz⟩ := this
        have : z - (x + r q₀) = c := by
          rw [show z - (x + r q₀) = (z - x) - r q₀ by abel, ← hcz]; abel
        rw [this]; exact hc
      · intro q _ hq
        rw [ite_eq_right]
        intro hmem
        apply hq
        apply Subtype.ext
        rw [← hrπ q]
        apply (QuotientAddGroup.mk'_eq_mk' L).mpr
        exact ⟨z - (x + r q), hmem, by abel⟩
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [indicator_of_notMem (show z ∉ S from hz)]
      refine (Finset.sum_eq_zero fun q _ => ?_).symm
      rw [ite_eq_right]
      intro hmem
      apply hz
      have : z - x = (z - (x + r q)) + r q := by abel
      rw [this]
      exact M.add_mem (hLM hmem) (hrM q)
  -- the number of cosets
  let N : ℕ := Fintype.card Q
  have hN : (N : ℂ) ≠ 0 := by
    have : 0 < N := Fintype.card_pos_iff.mpr ⟨⟨π 0, ⟨0, M.zero_mem, rfl⟩⟩⟩
    exact_mod_cast this.ne'
  have hTg : ∀ T : Distribution A, IsConjugationInvariant T →
      T g = (N : ℂ) * T (latticeCosetTest L hLo hLc x) := by
    intro T hT
    rw [hdec, map_sum]
    rw [Finset.sum_congr rfl fun q _ => hcos (x + r q) (by simpa using hrM q) T hT]
    simp [N]
  -- the conjugated average
  let f : SchwartzBruhat A :=
    (N : ℂ)⁻¹ • Hecke.TestFunction.pullback (conjugationHomeomorph γ⁻¹) g
  have hf : ∀ z, f z = (N : ℂ)⁻¹ * S.indicator (fun _ => (1 : ℂ))
      (((γ⁻¹ : Aˣ) : A) * z * γ) := by
    intro z
    simp only [f, g, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      Hecke.TestFunction.pullback_apply, conjugationHomeomorph_apply,
      Hecke.TestFunction.characteristic_apply, inv_inv]
  refine ⟨f, ?_, ?_, ?_⟩
  · intro t ht z
    rw [hf, hf]
    congr 1
    have hmem : ((γ⁻¹ : Aˣ) : A) * (z + t) * γ - x ∈ M ↔ ((γ⁻¹ : Aˣ) : A) * z * γ - x ∈ M := by
      have : ((γ⁻¹ : Aˣ) : A) * (z + t) * γ - x =
          (((γ⁻¹ : Aˣ) : A) * z * γ - x) + ((γ⁻¹ : Aˣ) : A) * t * γ := by
        rw [mul_add, add_mul]; abel
      rw [this]
      exact M.add_mem_cancel_right (hγ t ht)
    by_cases h : ((γ⁻¹ : Aˣ) : A) * z * γ - x ∈ M
    · rw [indicator_of_mem (show _ ∈ S from hmem.mpr h), indicator_of_mem (show _ ∈ S from h)]
    · rw [indicator_of_notMem (show _ ∉ S from fun h' => h (hmem.mp h')),
        indicator_of_notMem (show _ ∉ S from h)]
  · intro z hz
    rw [hf] at hz
    by_contra h
    rw [indicator_of_notMem (show _ ∉ S from h), mul_zero] at hz
    exact hz rfl
  · intro T hT
    have hpull : T (Hecke.TestFunction.pullback (conjugationHomeomorph γ⁻¹) g) = T g :=
      (isConjugationInvariant_iff T).mp hT γ⁻¹ g
    rw [map_smul, hpull, hTg T hT, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hN, one_mul]

end Averaging


section Grading

variable {F : Type*} [Field F] {A : Type*} [Ring A] [Algebra F A] {e : ℕ → A} {m : ℕ}

/-- The element `∑_{i < m} c i • e i` attached to orthogonal idempotents `e i`. -/
def idemSum (e : ℕ → A) (m : ℕ) (c : ℕ → F) : A := ∑ i ∈ range m, c i • e i

variable (he : ∀ i, e i * e i = e i) (horth : ∀ i j, i ≠ j → e i * e j = 0)
include he horth

theorem idemSum_mul_idemSum (c d : ℕ → F) :
    idemSum e m c * idemSum e m d = idemSum e m (fun i => c i * d i) := by
  unfold idemSum
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mul_sum, Finset.sum_eq_single i]
  · rw [smul_mul_smul_comm, he]
  · intro j _ hj
    rw [smul_mul_smul_comm, horth i j (Ne.symm hj), smul_zero]
  · intro h; exact absurd hi h

omit he horth in
theorem idemSum_mul_mul_idemSum (c d : ℕ → F) (Y : A) :
    idemSum e m c * Y * idemSum e m d =
      ∑ i ∈ range m, ∑ j ∈ range m, (c i * d j) • (e i * Y * e j) := by
  unfold idemSum
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc, mul_comm (d j)]

theorem mul_doubleSum_mul (f : ℕ → ℕ → F) (Y : A) {a b : ℕ} (ha : a < m) (hb : b < m) :
    e a * (∑ i ∈ range m, ∑ j ∈ range m, f i j • (e i * Y * e j)) * e b =
      f a b • (e a * Y * e b) := by
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_eq_single a]
  · rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_eq_single b]
    · rw [mul_smul_comm, smul_mul_assoc]
      congr 1
      have : e a * (e a * Y * e b) * e b = (e a * e a) * Y * (e b * e b) := by
        simp only [mul_assoc]
      rw [this, he, he]
    · intro j _ hj
      rw [mul_smul_comm, smul_mul_assoc]
      have : e a * (e a * Y * e j) * e b = e a * (e a * Y) * (e j * e b) := by
        simp only [mul_assoc]
      rw [this, horth j b hj, mul_zero, smul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr hb) h
  · intro i _ hi
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [mul_smul_comm, smul_mul_assoc]
    have : e a * (e i * Y * e j) * e b = (e a * e i) * (Y * e j * e b) := by
      simp only [mul_assoc]
    rw [this, horth a i (Ne.symm hi), zero_mul, smul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr ha) h

variable (hsum : ∑ i ∈ range m, e i = 1)
include hsum

omit he in
theorem eq_zero_of_ge {a : ℕ} (ha : m ≤ a) : e a = 0 := by
  rw [← mul_one (e a), ← hsum]
  exact mul_sum_range_of_le horth ha

omit he horth in
theorem eq_doubleSum (Y : A) : Y = ∑ i ∈ range m, ∑ j ∈ range m, e i * Y * e j := by
  calc Y = (∑ i ∈ range m, e i) * Y * (∑ j ∈ range m, e j) := by rw [hsum, one_mul, mul_one]
    _ = ∑ i ∈ range m, ∑ j ∈ range m, e i * Y * e j := by
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]

omit he in
/-- `e i Y e j = 0` for `i ≤ j` and all `i, j`, as soon as it holds for `i, j < m`. -/
theorem isLower_of_lt {Y : A} (hY : ∀ i j, i < m → j < m → i ≤ j → e i * Y * e j = 0) :
    ∀ i j, i ≤ j → e i * Y * e j = 0 := by
  intro i j hij
  by_cases hi : i < m
  · by_cases hj : j < m
    · exact hY i j hi hj hij
    · rw [eq_zero_of_ge horth hsum (not_lt.mp hj), mul_zero]
  · rw [eq_zero_of_ge horth hsum (not_lt.mp hi), zero_mul, zero_mul]

end Grading

section RightInverse

variable {F : Type*} [Field F] {A : Type*} [Ring A] [Algebra F A]

/-- A linear right inverse of `y ↦ x y - y x` on a subspace of its range. -/
theorem exists_linear_rightInverse_commutator (x : A) (N : Submodule F A)
    (hN : ∀ w ∈ N, ∃ y, x * y - y * x = w) :
    ∃ σ : A →ₗ[F] A, ∀ w ∈ N, x * σ w - σ w * x = w := by
  let D : A →ₗ[F] A := LinearMap.mulLeft F x - LinearMap.mulRight F x
  have hD : ∀ y, D y = x * y - y * x := fun y => rfl
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective D.rangeRestrict
    (LinearMap.range_rangeRestrict D)
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.range D)
  refine ⟨g ∘ₗ Submodule.projectionOnto (LinearMap.range D) C hC, fun w hw => ?_⟩
  obtain ⟨y, hy⟩ := hN w hw
  have hwr : w ∈ LinearMap.range D := ⟨y, by rw [hD, hy]⟩
  have hp : Submodule.projectionOnto (LinearMap.range D) C hC w = ⟨w, hwr⟩ :=
    Submodule.projectionOnto_apply_left hC ⟨w, hwr⟩
  have := congrArg Subtype.val (LinearMap.congr_fun hg ⟨w, hwr⟩)
  simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.codRestrict_apply] at this
  rw [← hD, LinearMap.comp_apply, hp]
  exact this

end RightInverse

section Core

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {A : Type*} [Ring A] [Algebra F A] [TopologicalSpace A] [IsModuleTopology F A]
  {R : Subring A} {ϖ : F}

/-- A linear map moves the levels `ϖ ^ k R` by a bounded amount. -/
theorem exists_orderLevel_bound (hR : IsCompactOpenOrder F R) (hϖ : ϖ ≠ 0)
    (hϖ1 : valuation F ϖ < 1) [IsNonarchimedeanLocalField F] [FiniteDimensional F A]
    (σ : A →ₗ[F] A) :
    ∃ b : ℕ, ∀ (k : ℤ) (w : A), w ∈ orderLevel R ϖ k → σ w ∈ orderLevel R ϖ (k - b) := by
  have := IsModuleTopology.toContinuousAdd F A
  have hc : Continuous σ := IsModuleTopology.continuous_of_linearMap σ
  have hU : σ ⁻¹' (R : Set A) ∈ nhds (0 : A) := by
    apply hc.continuousAt.preimage_mem_nhds
    rw [map_zero]
    exact hR.isOpen.mem_nhds R.zero_mem
  obtain ⟨b, hb⟩ := exists_orderLevel_subset hR hϖ hϖ1 hU
  refine ⟨b, fun k w hw => ?_⟩
  have h1 : ϖ ^ ((b : ℤ) - k) • w ∈ orderLevel R ϖ b := by
    have := (zpow_smul_mem_orderLevel_iff hϖ ((b : ℤ) - k) k w).mpr hw
    simpa using this
  have h2 : ϖ ^ ((b : ℤ) - k) • σ w ∈ orderLevel R ϖ ((k - b) + ((b : ℤ) - k)) := by
    rw [← map_smul]
    simpa using hb h1
  exact (zpow_smul_mem_orderLevel_iff hϖ _ _ _).mp h2

omit [TopologicalSpace F] [TopologicalSpace A] [IsModuleTopology F A] in
/-- A double sum `∑ ϖ ^ (f i j) • e i Y e j` of graded pieces of `Y ∈ ϖ ^ k R` lies in
`ϖ ^ k' R` when every nonzero piece is moved to level at least `k'`. -/
theorem doubleSum_mem_orderLevel (hϖ : ϖ ≠ 0)
    (hsmul : ∀ c : F, valuation F c ≤ 1 → ∀ x ∈ R, c • x ∈ R) (hϖ1 : valuation F ϖ < 1)
    {e : ℕ → A} (heR : ∀ i, e i ∈ R) (m : ℕ)
    (f : ℕ → ℕ → ℤ) {k k' : ℤ} {Y : A} (hY : Y ∈ orderLevel R ϖ k)
    (hf : ∀ i j, i < m → j < m → e i * Y * e j = 0 ∨ k' ≤ k + f i j) :
    ∑ i ∈ range m, ∑ j ∈ range m, ϖ ^ (f i j) • (e i * Y * e j) ∈ orderLevel R ϖ k' := by
  refine AddSubgroup.sum_mem _ fun i hi => AddSubgroup.sum_mem _ fun j hj => ?_
  rcases hf i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) with h0 | hle
  · rw [h0, smul_zero]; exact AddSubgroup.zero_mem _
  · have hmem : e i * Y * e j ∈ orderLevel R ϖ k :=
      mul_mem_orderLevel_right hϖ (heR j) (mul_mem_orderLevel_left hϖ (heR i) hY)
    have := (zpow_smul_mem_orderLevel_iff hϖ (f i j) k _).mpr hmem
    exact orderLevel_anti hϖ hsmul hϖ1 hle this

omit [ValuativeRel F] [TopologicalSpace F] [IsModuleTopology F A] in
theorem latticeCosetTest_eq_pullback_conj [IsTopologicalRing A] (L : AddSubgroup A)
    (hLo : IsOpen (L : Set A)) (hLc : IsCompact (L : Set A)) (g : Aˣ)
    (hgL : ∀ t ∈ L, (g : A) * t * ((g⁻¹ : Aˣ) : A) ∈ L)
    (hg'L : ∀ t ∈ L, ((g⁻¹ : Aˣ) : A) * t * g ∈ L) {x y : A}
    (hxy : (g : A) * x * ((g⁻¹ : Aˣ) : A) - y ∈ L) :
    latticeCosetTest L hLo hLc y =
      Hecke.TestFunction.pullback (conjugationHomeomorph g⁻¹) (latticeCosetTest L hLo hLc x) := by
  classical
  apply Hecke.TestFunction.ext
  intro z
  rw [Hecke.TestFunction.pullback_apply, latticeCosetTest_apply_eq, latticeCosetTest_apply_eq,
    conjugationHomeomorph_apply, inv_inv]
  have hgi : ((g⁻¹ : Aˣ) : A) * g = 1 := Units.inv_mul g
  have hid : ((g⁻¹ : Aˣ) : A) * z * g - x =
      ((g⁻¹ : Aˣ) : A) * (z - y) * g + ((g⁻¹ : Aˣ) : A) * (y - g * x * ((g⁻¹ : Aˣ) : A)) * g := by
    have : ((g⁻¹ : Aˣ) : A) * (z - y) * g + ((g⁻¹ : Aˣ) : A) * (y - g * x * ((g⁻¹ : Aˣ) : A)) * g =
        ((g⁻¹ : Aˣ) : A) * z * g - (((g⁻¹ : Aˣ) : A) * g) * x * (((g⁻¹ : Aˣ) : A) * g) := by
      noncomm_ring
    rw [this, hgi, one_mul, mul_one]
  have hmem : ((g⁻¹ : Aˣ) : A) * (y - g * x * ((g⁻¹ : Aˣ) : A)) * g ∈ L := by
    apply hg'L
    rw [← neg_sub]
    exact L.neg_mem hxy
  have hiff : ((g⁻¹ : Aˣ) : A) * z * g - x ∈ L ↔ z - y ∈ L := by
    rw [hid, L.add_mem_cancel_right hmem]
    constructor
    · intro h
      have := hgL _ h
      simpa [mul_assoc] using this
    · exact hg'L _
  by_cases h : z - y ∈ L
  · rw [ite_eq_left h, ite_eq_left (hiff.mpr h)]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hiff.mp h'))]

variable (hR : IsCompactOpenOrder F R) (hϖ : ϖ ≠ 0) (hϖ1 : valuation F ϖ < 1)
include hR hϖ hϖ1

/-- **The Newton step.** If `X y - y X = w` with `w ∈ ϖ ^ c R` and `y ∈ ϖ ^ (c - b) R`, then for
`h` large the unit `g = 1 - ϖ ^ h y` of `R` conjugates `ϖ ^ (-h) (X + λ)` to
`ϖ ^ (-h) (X + λ) + w` modulo `ϖ ^ s R`, provided `λ ∈ ϖ ^ (s - c + b) R`. -/
theorem exists_unit_conj_sub_mem [IsNonarchimedeanLocalField F] [FiniteDimensional F A]
    {s c b : ℤ} (hcs : c ≤ s) {X lam w y : A} (hw : w ∈ orderLevel R ϖ c)
    (hy : y ∈ orderLevel R ϖ (c - b))
    (hXy : X * y - y * X = w) (hlam : lam ∈ orderLevel R ϖ (s - c + b)) (h : ℕ)
    (hh1 : 1 ≤ (h : ℤ) + c - b) (hh2 : s ≤ (h : ℤ) + 2 * c - b) :
    ∃ g : Aˣ, (g : A) ∈ R ∧ ((g⁻¹ : Aˣ) : A) ∈ R ∧
      (g : A) * (ϖ ^ (-(h : ℤ)) • (X + lam)) * ((g⁻¹ : Aˣ) : A) -
        ϖ ^ (-(h : ℤ)) • (X + lam) - w ∈ orderLevel R ϖ s := by
  set u : A := -(ϖ ^ (h : ℤ) • y) with hu_def
  have hu : u ∈ orderLevel R ϖ ((c - b) + h) :=
    (orderLevel R ϖ _).neg_mem ((zpow_smul_mem_orderLevel_iff hϖ (h : ℤ) (c - b) y).mpr hy)
  have hu1 : u ∈ orderLevel R ϖ 1 := orderLevel_anti hϖ hR.smul_mem hϖ1 (by omega) hu
  have hu0 : u ∈ R := mem_orderLevel_zero.mp (orderLevel_anti hϖ hR.smul_mem hϖ1 (by omega) hu1)
  obtain ⟨v, hvR, hv1, hv2⟩ := exists_inverse_one_add hR hϖ hϖ1 hu1
  let g : Aˣ := ⟨1 + u, v, hv1, hv2⟩
  refine ⟨g, R.add_mem R.one_mem hu0, hvR, ?_⟩
  change (1 + u) * (ϖ ^ (-(h : ℤ)) • (X + lam)) * v - ϖ ^ (-(h : ℤ)) • (X + lam) - w ∈ _
  set x : A := ϖ ^ (-(h : ℤ)) • (X + lam) with hx_def
  set δ : A := lam * y - y * lam with hδ_def
  have hcancel : ϖ ^ (h : ℤ) * ϖ ^ (-(h : ℤ)) = 1 := by rw [← zpow_add₀ hϖ]; simp
  have hcancel' : ϖ ^ (-(h : ℤ)) * ϖ ^ (h : ℤ) = 1 := by rw [← zpow_add₀ hϖ]; simp
  have hux : u * x = -(y * (X + lam)) := by
    rw [hu_def, hx_def, neg_mul, smul_mul_smul_comm, hcancel, one_smul]
  have hxu : x * u = -((X + lam) * y) := by
    rw [hu_def, hx_def, mul_neg, smul_mul_smul_comm, hcancel', one_smul]
  have hE : u * x - x * u = w + δ := by
    rw [hux, hxu, hδ_def, ← hXy]
    noncomm_ring
  have hxv : x * v + x * u * v = x := by
    rw [mul_assoc, ← mul_add, ← one_add_mul, hv1, mul_one]
  have key : (1 + u) * x * v - x - w = δ + (w + δ) * (v - 1) := by
    have : (1 + u) * x * v - x - w - (δ + (u * x - x * u) * (v - 1)) =
        (x * v + x * u * v - x) + ((u * x - x * u) - (w + δ)) := by
      noncomm_ring
    rw [hxv, hE, sub_self, sub_self, add_zero] at this
    exact sub_eq_zero.mp this
  rw [key]
  have hδ : δ ∈ orderLevel R ϖ s := by
    have h1 := mul_mem_orderLevel hϖ hlam hy
    have h2 := mul_mem_orderLevel hϖ hy hlam
    have e1 : s - c + b + (c - b) = s := by ring
    have e2 : c - b + (s - c + b) = s := by ring
    rw [e1] at h1; rw [e2] at h2
    exact (orderLevel R ϖ s).sub_mem h1 h2
  have hEc : w + δ ∈ orderLevel R ϖ c :=
    (orderLevel R ϖ c).add_mem hw (orderLevel_anti hϖ hR.smul_mem hϖ1 hcs hδ)
  have hv1' : v - 1 = -(u * v) := by
    have : v + u * v = 1 := by rw [← one_add_mul]; exact hv1
    rw [← this]; abel
  refine (orderLevel R ϖ s).add_mem hδ ?_
  rw [hv1', mul_neg]
  refine (orderLevel R ϖ s).neg_mem ?_
  have hm := mul_mem_orderLevel_right hϖ hvR (mul_mem_orderLevel hϖ hEc hu)
  rw [← mul_assoc]
  exact orderLevel_anti hϖ hR.smul_mem hϖ1 (by omega) hm

/-- **Decreasing averages near a graded nilpotent element.** Let `e 0, …, e (m - 1)` be
orthogonal idempotents of the order `R` with sum `1`, and let `X₀ ∈ R` satisfy
`e i X₀ e j = 0` for `i ≤ j`, such that every `w` with `e i w e j = 0` for `i ≤ j` is a
commutator `X₀ y - y X₀`. Then for every lattice `L = ϖ ^ s R` there are `a, t` such that for
`h ≥ t` and `λ ∈ ϖ ^ a R` the indicator of the coset `x + L`, `x = ϖ ^ (-h) (X₀ + λ)`, has the
same value under every conjugation-invariant distribution as an `L`-invariant test supported
in `ϖ ^ (1 - h) R`. -/
theorem exists_decreasing_average [IsNonarchimedeanLocalField F] [FiniteDimensional F A]
    [IsTopologicalRing A] {e : ℕ → A} {m : ℕ} (heR : ∀ i, e i ∈ R)
    (he : ∀ i, e i * e i = e i) (horth : ∀ i j, i ≠ j → e i * e j = 0)
    (hsum : ∑ i ∈ range m, e i = 1) (s : ℤ) {X₀ : A} (hX₀R : X₀ ∈ R)
    (hX₀ : ∀ i j, i ≤ j → e i * X₀ * e j = 0)
    (hsurj : ∀ w, (∀ i j, i ≤ j → e i * w * e j = 0) → ∃ y, X₀ * y - y * X₀ = w) :
    ∃ a t : ℕ, ∀ h : ℕ, t ≤ h → ∀ lam ∈ orderLevel R ϖ a,
      ∃ f : SchwartzBruhat A, f ∈ latticeInvariantTests (orderLevel R ϖ s) ∧
        (∀ z, f z ≠ 0 → z ∈ orderLevel R ϖ (-(h : ℤ) + 1)) ∧
        ∀ T : Distribution A, IsConjugationInvariant T →
          T f = T (latticeCosetTest (orderLevel R ϖ s) (isOpen_orderLevel hR s)
            (isCompact_orderLevel hR hϖ s) (ϖ ^ (-(h : ℤ)) • (X₀ + lam))) := by
  classical
  let nSub : Submodule F A :=
    { carrier := {w | ∀ i j, i ≤ j → e i * w * e j = 0}
      add_mem' := fun {a b} ha hb i j hij => by
        simp only [Set.mem_ofPred_eq] at ha hb
        rw [mul_add, add_mul, ha i j hij, hb i j hij, add_zero]
      zero_mem' := fun i j _ => by simp
      smul_mem' := fun c w hw i j hij => by
        simp only [Set.mem_ofPred_eq] at hw ⊢
        rw [mul_smul_comm, smul_mul_assoc, hw i j hij, smul_zero] }
  obtain ⟨σ, hσ⟩ := exists_linear_rightInverse_commutator X₀ nSub (fun w hw => hsurj w hw)
  obtain ⟨b, hb⟩ := exists_orderLevel_bound hR hϖ hϖ1 σ
  have hsabs1 : s ≤ (s.natAbs : ℤ) := Int.le_natAbs
  have hsabs2 : -s ≤ (s.natAbs : ℤ) := by
    have := Int.le_natAbs (a := -s); rwa [Int.natAbs_neg] at this
  refine ⟨m + b, 2 * m + b + s.natAbs + 1, fun h hh lam hlam => ?_⟩
  have hhz : (2 * m + b + s.natAbs + 1 : ℤ) ≤ h := by exact_mod_cast hh
  let L := orderLevel R ϖ s
  have hLo : IsOpen (L : Set A) := isOpen_orderLevel hR s
  have hLc : IsCompact (L : Set A) := isCompact_orderLevel hR hϖ s
  set x : A := ϖ ^ (-(h : ℤ)) • (X₀ + lam) with hx_def
  -- the grading unit
  let γ : A := idemSum e m (fun i => ϖ ^ (i : ℤ))
  let γ' : A := idemSum e m (fun i => ϖ ^ (-(i : ℤ)))
  have hidem1 : idemSum e m (fun _ => (1 : F)) = 1 := by
    simp [idemSum, hsum]
  have hγγ' : γ * γ' = 1 := by
    rw [idemSum_mul_idemSum he horth, ← hidem1]
    unfold idemSum
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only
    rw [← zpow_add₀ hϖ, add_neg_cancel, zpow_zero]
  have hγ'γ : γ' * γ = 1 := by
    rw [idemSum_mul_idemSum he horth, ← hidem1]
    unfold idemSum
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only
    rw [← zpow_add₀ hϖ, neg_add_cancel, zpow_zero]
  let γu : Aˣ := ⟨γ, γ', hγγ', hγ'γ⟩
  have hconj : ∀ Y, γ * Y * γ' =
      ∑ i ∈ range m, ∑ j ∈ range m, ϖ ^ ((i : ℤ) - j) • (e i * Y * e j) := by
    intro Y
    rw [idemSum_mul_mul_idemSum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← zpow_add₀ hϖ, sub_eq_add_neg]
  have hconj' : ∀ Y, γ' * Y * γ =
      ∑ i ∈ range m, ∑ j ∈ range m, ϖ ^ ((j : ℤ) - i) • (e i * Y * e j) := by
    intro Y
    rw [idemSum_mul_mul_idemSum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← zpow_add₀ hϖ, sub_eq_add_neg, add_comm]
  -- the group `M = L + γ⁻¹ L γ`
  let φ : A →+ A := (AddMonoidHom.mulLeft γ').comp (AddMonoidHom.mulRight γ)
  have hφ : ∀ Y, φ Y = γ' * Y * γ := fun Y => by
    simp [φ, mul_assoc]
  let M : AddSubgroup A := L ⊔ L.map φ
  have hmemM : ∀ z, z ∈ M ↔ ∃ ℓ₁ ∈ L, ∃ ℓ₂ ∈ L, ℓ₁ + γ' * ℓ₂ * γ = z := by
    intro z
    rw [AddSubgroup.mem_sup]
    constructor
    · rintro ⟨ℓ₁, h₁, _, ⟨ℓ₂, h₂, rfl⟩, rfl⟩
      exact ⟨ℓ₁, h₁, ℓ₂, h₂, by rw [hφ]⟩
    · rintro ⟨ℓ₁, h₁, ℓ₂, h₂, rfl⟩
      exact ⟨ℓ₁, h₁, φ ℓ₂, ⟨ℓ₂, h₂, rfl⟩, by rw [hφ]⟩
  have hMc : IsCompact (M : Set A) := by
    have : (M : Set A) = (fun p : A × A => p.1 + γ' * p.2 * γ) '' ((L : Set A) ×ˢ (L : Set A)) := by
      ext z
      rw [SetLike.mem_coe, hmemM]
      constructor
      · rintro ⟨ℓ₁, h₁, ℓ₂, h₂, rfl⟩; exact ⟨(ℓ₁, ℓ₂), ⟨h₁, h₂⟩, rfl⟩
      · rintro ⟨⟨ℓ₁, ℓ₂⟩, ⟨h₁, h₂⟩, rfl⟩; exact ⟨ℓ₁, h₁, ℓ₂, h₂, rfl⟩
    rw [this]
    exact (hLc.prod hLc).image (continuous_fst.add
      ((continuous_const.mul continuous_snd).mul continuous_const))
  have hγL : ∀ t ∈ L, ((γu⁻¹ : Aˣ) : A) * t * γu ∈ M := by
    intro t ht
    exact (hmemM _).mpr ⟨0, L.zero_mem, t, ht, by simp [γu]⟩
  -- level bookkeeping
  have hsm : ∀ {i j : ℕ}, i < m → j < m → (-(m : ℤ)) ≤ (j : ℤ) - i := by
    intro i j hi hj; omega
  -- all cosets in `x + M` have the same invariant values
  have hcos : ∀ y, y - x ∈ M → ∀ T : Distribution A, IsConjugationInvariant T →
      T (latticeCosetTest L hLo hLc y) = T (latticeCosetTest L hLo hLc x) := by
    intro y hy T hT
    obtain ⟨ℓ₁, h₁, ℓ₂, h₂, hyx⟩ := (hmemM _).mp hy
    let w : A := ∑ i ∈ range m, ∑ j ∈ range m,
      (if j < i then ϖ ^ ((j : ℤ) - i) else 0) • (e i * ℓ₂ * e j)
    let q : A := ∑ i ∈ range m, ∑ j ∈ range m,
      (if j < i then 0 else ϖ ^ ((j : ℤ) - i)) • (e i * ℓ₂ * e j)
    have hwq : γ' * ℓ₂ * γ = w + q := by
      rw [hconj', ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← add_smul]
      split_ifs <;> simp
    have hpiece : ∀ i j, e i * ℓ₂ * e j ∈ L := fun i j =>
      mul_mem_orderLevel_right hϖ (heR j) (mul_mem_orderLevel_left hϖ (heR i) h₂)
    have hwn : w ∈ nSub := by
      refine isLower_of_lt horth hsum fun i j hi hj hij => ?_
      rw [mul_doubleSum_mul he horth _ _ hi hj, ite_eq_right (by omega), zero_smul]
    have hwc : w ∈ orderLevel R ϖ (s - m) := by
      refine AddSubgroup.sum_mem _ fun i hi => AddSubgroup.sum_mem _ fun j hj => ?_
      split_ifs with hji
      · have := (zpow_smul_mem_orderLevel_iff hϖ ((j : ℤ) - i) s _).mpr (hpiece i j)
        exact orderLevel_anti hϖ hR.smul_mem hϖ1
          (by have := hsm (Finset.mem_range.mp hi) (Finset.mem_range.mp hj); omega) this
      · rw [zero_smul]; exact AddSubgroup.zero_mem _
    have hqL : q ∈ L := by
      refine AddSubgroup.sum_mem _ fun i hi => AddSubgroup.sum_mem _ fun j hj => ?_
      split_ifs with hji
      · rw [zero_smul]; exact AddSubgroup.zero_mem _
      · have := (zpow_smul_mem_orderLevel_iff hϖ ((j : ℤ) - i) s _).mpr (hpiece i j)
        exact orderLevel_anti hϖ hR.smul_mem hϖ1 (by omega) this
    have hyw : y - (x + w) ∈ L := by
      have : y - (x + w) = ℓ₁ + q := by
        rw [← sub_sub, ← hyx, hwq]; abel
      rw [this]; exact L.add_mem h₁ hqL
    have hσw := hb (s - m) w hwc
    have hlam' : lam ∈ orderLevel R ϖ (s - (s - m) + b) := by
      have : s - (s - m) + b = ((m + b : ℕ) : ℤ) := by push_cast; ring
      rw [this]; exact hlam
    obtain ⟨g, hgR, hg'R, hg⟩ := exists_unit_conj_sub_mem hR hϖ hϖ1 (s := s) (c := s - m)
      (b := b) (by omega) hwc hσw (hσ w hwn) hlam' h (by omega) (by omega)
    have hxy : (g : A) * x * ((g⁻¹ : Aˣ) : A) - y ∈ L := by
      have : (g : A) * x * ((g⁻¹ : Aˣ) : A) - y =
          ((g : A) * x * ((g⁻¹ : Aˣ) : A) - x - w) - (y - (x + w)) := by abel
      rw [this]; exact L.sub_mem hg hyw
    rw [latticeCosetTest_eq_pullback_conj L hLo hLc g
      (fun t ht => mul_mem_orderLevel_right hϖ hg'R (mul_mem_orderLevel_left hϖ hgR ht))
      (fun t ht => mul_mem_orderLevel_right hϖ hgR (mul_mem_orderLevel_left hϖ hg'R ht)) hxy]
    exact (isConjugationInvariant_iff T).mp hT g⁻¹ _
  obtain ⟨f, hfL, hfsupp, hfT⟩ :=
    exists_conj_average L hLo hLc M le_sup_left hMc γu hγL x hcos
  refine ⟨f, hfL, fun z hz => ?_, hfT⟩
  have hzM := hfsupp z hz
  change γ' * z * γ - x ∈ M at hzM
  obtain ⟨ℓ₁, h₁, ℓ₂, h₂, hzx⟩ := (hmemM _).mp hzM
  have hz_eq : z = γ * x * γ' + γ * ℓ₁ * γ' + ℓ₂ := by
    have hz1 : z = γ * (γ' * z * γ) * γ' := by
      rw [← mul_assoc, ← mul_assoc, hγγ', one_mul, mul_assoc, hγγ', mul_one]
    have hz2 : γ' * z * γ = x + ℓ₁ + γ' * ℓ₂ * γ := by
      rw [sub_eq_iff_eq_add'.mp hzx.symm, add_assoc]
    rw [hz1, hz2]
    simp only [mul_add, add_mul]
    congr 1
    rw [← mul_assoc, ← mul_assoc, hγγ', one_mul, mul_assoc, hγγ', mul_one]
  rw [hz_eq]
  refine AddSubgroup.add_mem _ (AddSubgroup.add_mem _ ?_ ?_) ?_
  · have hX : γ * X₀ * γ' ∈ orderLevel R ϖ 1 := by
      rw [hconj]
      refine doubleSum_mem_orderLevel hϖ hR.smul_mem hϖ1 heR m _
        (mem_orderLevel_zero.mpr hX₀R) fun i j _ _ => ?_
      by_cases hij : i ≤ j
      · exact Or.inl (hX₀ i j hij)
      · right; omega
    have hl : γ * lam * γ' ∈ orderLevel R ϖ 1 := by
      rw [hconj]
      refine doubleSum_mem_orderLevel hϖ hR.smul_mem hϖ1 heR m _ hlam fun i j hi hj => ?_
      right; push_cast; omega
    have hsum1 : γ * (X₀ + lam) * γ' ∈ orderLevel R ϖ 1 := by
      rw [mul_add, add_mul]; exact AddSubgroup.add_mem _ hX hl
    have : γ * x * γ' = ϖ ^ (-(h : ℤ)) • (γ * (X₀ + lam) * γ') := by
      rw [hx_def, mul_smul_comm, smul_mul_assoc]
    rw [this]
    have := (zpow_smul_mem_orderLevel_iff hϖ (-(h : ℤ)) 1 _).mpr hsum1
    rwa [add_comm] at this
  · rw [hconj]
    refine doubleSum_mem_orderLevel hϖ hR.smul_mem hϖ1 heR m _ h₁ fun i j hi hj => ?_
    right; omega
  · exact orderLevel_anti hϖ hR.smul_mem hϖ1 (by omega) h₂

end Core

end Langlands.HarmonicAnalysis.UnitConjugation
