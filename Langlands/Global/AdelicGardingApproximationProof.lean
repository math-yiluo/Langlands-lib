import Langlands.Global.AdelicTemperedComponentInputs
import Langlands.Representation.Archimedean.GardingDensity
import Langlands.Global.FiniteAdelicGroupCompactOpenBasisProof
import Langlands.Global.AdelicGroupPolish
import Langlands.Global.InfiniteAdelicGroupManifold

/-! # Gårding smoothing on `G(𝔸)`

`Langlands.Global.adelicGardingApproximation` proves `AdelicGardingApproximationStatement`.

The construction is carried out on an abstract topological group `A` with a topological group
isomorphism `s : A ≃ X × Y`, where `X` is a real Lie group and the identity of `Y` has a basis of
compact open subgroups; it is then applied to `AdelicGroupPoints.split`, with `X = G(F_∞)` and
`Y = G(𝔸_f)`. For a smooth compactly supported weight `b` on `X`, a compact open subgroup `K` of
`Y` and a constant `k`, the kernel `kernel s b K k` is `g ↦ k · b(x) · 1_K(y)` at `s g = (x, y)`.

* `integral_eq_smul_integral_integral`: the image of a Haar measure of `A` under `s` is a constant
  `splitHaarFactor` times the product of Haar measures of `X` and `Y` (uniqueness of Haar measure
  on the second countable group `X × Y`), so integrals over `A` are iterated integrals.
* `integral_kernel_smul`: `∫ kernel(g) ρ(g) u dg = c k ∫_X b(x) ρ(x) w dx` with
  `w = ∫_Y 1_K(y) ρ(y) u dy`; by `Langlands.Archimedean.isSmoothVector_gardingIntegral` this is a
  smooth vector for the restriction of `ρ` to `X`.
* `integral_kernel_smul_invariant`: the kernel is invariant under left translation by `K`, so the
  averaged vector is fixed by `ρ(K)` (left invariance of Haar measure).
* `tendsto_integral_smul`: kernels with integral `1`, `L¹`-norm `1` and supports shrinking to the
  identity give `ρ(ψ_n) u → u` for every jointly continuous representation `ρ`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped Manifold ENNReal NNReal ContDiff

set_option autoImplicit false

namespace Langlands.Global.AdelicGardingApproximation

/-- The integral of the complex indicator function of a measurable set is its volume. -/
theorem integral_indicator_one_complex {Y : Type*} [MeasurableSpace Y] (μY : Measure Y)
    {K : Set Y} (hK : MeasurableSet K) :
    ∫ y, K.indicator (1 : Y → ℂ) y ∂μY = (μY.real K : ℂ) := by
  have h := integral_indicator_const (μ := μY) (1 : ℂ) hK
  rw [Complex.real_smul, mul_one] at h
  exact h

section Kernel

variable {A X Y : Type*} [Group A] [TopologicalSpace A] [Group X] [TopologicalSpace X]
  [Group Y] [TopologicalSpace Y] (s : A ≃ₜ* X × Y)

/-- The kernel `k · b(x) · 1_K(y)` at the point `g` with `s g = (x, y)`. -/
def kernel (b : X → ℂ) (K : Set Y) (k : ℂ) (g : A) : ℂ :=
  k * b (s g).1 * K.indicator 1 (s g).2

theorem kernel_symm (b : X → ℂ) (K : Set Y) (k : ℂ) (x : X) (y : Y) :
    kernel s b K k (s.symm (x, y)) = k * b x * K.indicator 1 y := by
  simp [kernel]

theorem continuous_kernel {b : X → ℂ} (hb : Continuous b) {K : Set Y} (hK : IsClopen K)
    (k : ℂ) : Continuous (kernel s b K k) :=
  (continuous_const.mul (hb.comp (continuous_fst.comp (map_continuous s)))).mul
    ((hK.continuous_indicator continuous_one).comp (continuous_snd.comp (map_continuous s)))

theorem kernel_ne_zero {b : X → ℂ} {K : Set Y} {k : ℂ} {g : A} (h : kernel s b K k g ≠ 0) :
    b (s g).1 ≠ 0 ∧ (s g).2 ∈ K :=
  ⟨right_ne_zero_of_mul (left_ne_zero_of_mul h),
    Set.mem_of_indicator_ne_zero (right_ne_zero_of_mul h)⟩

/-- A function vanishing off `s⁻¹(T₁ × T₂)` for compact `T₁`, `T₂` is compactly supported. -/
theorem hasCompactSupport_of_split [T2Space A] {E : Type*} [Zero E] (f : A → E)
    {T₁ : Set X} {T₂ : Set Y} (h₁ : IsCompact T₁) (h₂ : IsCompact T₂)
    (hf : ∀ g, f g ≠ 0 → (s g).1 ∈ T₁ ∧ (s g).2 ∈ T₂) : HasCompactSupport f := by
  refine HasCompactSupport.intro ((h₁.prod h₂).image s.symm.continuous) fun g hg => ?_
  by_contra h
  obtain ⟨g₁, g₂⟩ := hf g h
  exact hg ⟨s g, ⟨g₁, g₂⟩, s.symm_apply_apply g⟩

theorem hasCompactSupport_kernel [T2Space A] {b : X → ℂ} (hb : HasCompactSupport b)
    {K : Set Y} (hK : IsCompact K) (k : ℂ) : HasCompactSupport (kernel s b K k) :=
  hasCompactSupport_of_split s _ hb hK fun _ hg =>
    ⟨subset_tsupport _ (kernel_ne_zero s hg).1, (kernel_ne_zero s hg).2⟩

/-- The kernel is invariant under left translation by `s⁻¹(1, l)` for `l ∈ K`. -/
theorem kernel_mul_left (b : X → ℂ) (K : Subgroup Y) (k : ℂ) {l : Y} (hl : l ∈ K) (g : A) :
    kernel s b K k (s.symm (1, l) * g) = kernel s b K k g := by
  have h : (K : Set Y).indicator (1 : Y → ℂ) (l * (s g).2) = (K : Set Y).indicator 1 (s g).2 := by
    by_cases h : (s g).2 ∈ K
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (K.mul_mem hl h), Pi.one_apply,
        Pi.one_apply]
    · rw [Set.indicator_of_notMem h,
        Set.indicator_of_notMem fun h' => h ((K.mul_mem_cancel_left hl).mp h')]
  simp only [kernel, map_mul, ContinuousMulEquiv.apply_symm_apply, Prod.fst_mul, Prod.snd_mul,
    one_mul, h]

theorem norm_kernel (b : X → ℂ) (K : Set Y) (k : ℂ) (g : A) :
    ‖kernel s b K k g‖ = (‖k‖ * ‖b (s g).1‖) * K.indicator (1 : Y → ℝ) (s g).2 := by
  rw [kernel, norm_mul, norm_mul]
  congr 1
  by_cases h : (s g).2 ∈ K <;> simp [h]

theorem continuous_of_eq_symm_one_left (ιY : Y →* A) (hιY : ∀ y, ιY y = s.symm (1, y)) :
    Continuous ιY := by
  have h : (ιY : Y → A) = fun y => s.symm (1, y) := funext hιY
  rw [h]
  exact (map_continuous s.symm).comp (continuous_const.prodMk continuous_id)

theorem continuous_of_eq_symm_one_right (ιX : X →* A) (hιX : ∀ x, ιX x = s.symm (x, 1)) :
    Continuous ιX := by
  have h : (ιX : X → A) = fun x => s.symm (x, 1) := funext hιX
  rw [h]
  exact (map_continuous s.symm).comp (continuous_id.prodMk continuous_const)

/-- The supports of kernels built on shrinking neighbourhood bases shrink to the identity. -/
theorem eventually_kernel_ne_zero_mem {U : ℕ → Set X} (hU : (𝓝 (1 : X)).HasAntitoneBasis U)
    {V : ℕ → Set Y} (hV : (𝓝 (1 : Y)).HasAntitoneBasis V) (b : ℕ → X → ℂ)
    (hbU : ∀ n, tsupport (b n) ⊆ U n) (K : ℕ → Set Y) (hKV : ∀ n, K n ⊆ V n) (k : ℕ → ℂ)
    {W : Set A} (hW : W ∈ 𝓝 (1 : A)) :
    ∀ᶠ n in atTop, ∀ g, kernel s (b n) (K n) (k n) g ≠ 0 → g ∈ W := by
  have h1 : (fun p : X × Y => s.symm p) ⁻¹' W ∈ 𝓝 ((1 : X), (1 : Y)) := by
    apply (map_continuous s.symm).continuousAt.preimage_mem_nhds
    rw [Prod.mk_one_one, map_one]
    exact hW
  rw [nhds_prod_eq] at h1
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := mem_prod_iff.mp h1
  filter_upwards [hU.eventually_subset ht₁, hV.eventually_subset ht₂] with n h₁ h₂ g hg
  obtain ⟨hb', hK'⟩ := kernel_ne_zero s hg
  have hmem : s g ∈ t₁ ×ˢ t₂ := ⟨h₁ (hbU n (subset_tsupport _ hb')), h₂ (hKV n hK')⟩
  simpa using hsub hmem

end Kernel

section Invariance

variable {A X Y : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [T2Space A]
  [MeasurableSpace A] [BorelSpace A] [Group X] [TopologicalSpace X]
  [Group Y] [TopologicalSpace Y] (s : A ≃ₜ* X × Y) (μ : Measure A) [μ.IsHaarMeasure]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The averaged vector is fixed by `ρ(s⁻¹(1, l))` for `l ∈ K`. -/
theorem integral_kernel_smul_invariant (ρ : A →* (E →L[ℂ] E))
    (hρ : Langlands.Archimedean.IsContinuousRepresentation ρ) (u : E)
    (ιY : Y →* A) (hιY : ∀ y, ιY y = s.symm (1, y))
    {b : X → ℂ} (hb : Continuous b) (hbc : HasCompactSupport b)
    (K : Subgroup Y) (hK : IsClopen (K : Set Y)) (hKc : IsCompact (K : Set Y)) (k : ℂ)
    {l : Y} (hl : l ∈ K) :
    ρ (ιY l) (∫ g, kernel s b K k g • ρ g u ∂μ) = ∫ g, kernel s b K k g • ρ g u ∂μ := by
  have horb : Continuous fun g => ρ g u := hρ.comp (continuous_id.prodMk continuous_const)
  have hint : Integrable (fun g => kernel s b K k g • ρ g u) μ :=
    ((continuous_kernel s hb hK k).smul horb).integrable_of_hasCompactSupport
      (hasCompactSupport_kernel s hbc hKc k).smul_right
  rw [← ContinuousLinearMap.integral_comp_comm _ hint]
  have h : ∀ g, ρ (ιY l) (kernel s b K k g • ρ g u) =
      kernel s b K k (ιY l * g) • ρ (ιY l * g) u := by
    intro g
    rw [map_smul, map_mul, mul_apply_eq_comp, hιY, kernel_mul_left s b K k hl]
  simp_rw [h]
  exact integral_mul_left_eq_self (fun g => kernel s b K k g • ρ g u) (ιY l)

end Invariance

section HaarProduct

variable {A X Y : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [T2Space A]
  [MeasurableSpace A] [BorelSpace A]
  [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [LocallyCompactSpace Y]
  [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
  (s : A ≃ₜ* X × Y) (μ : Measure A) [μ.IsHaarMeasure] (μX : Measure X) [μX.IsHaarMeasure]
  (μY : Measure Y) [μY.IsHaarMeasure]

/-- The constant comparing the image of `μ` under `s` with the product of `μX` and `μY`. -/
def splitHaarFactor : ℝ≥0 := Measure.haarScalarFactor (μ.map s) (μX.prod μY)

omit [T2Space A] in
theorem map_eq_splitHaarFactor_smul_prod :
    μ.map s = splitHaarFactor s μ μX μY • μX.prod μY :=
  Measure.isMulLeftInvariant_eq_smul (μ.map s) (μX.prod μY)

omit [T2Space A] in
theorem splitHaarFactor_pos : 0 < splitHaarFactor s μ μX μY := by
  refine pos_iff_ne_zero.mpr fun h => ?_
  have h0 := map_eq_splitHaarFactor_smul_prod s μ μX μY
  rw [h, zero_smul] at h0
  exact NeZero.ne μ ((Measure.map_eq_zero_iff (map_continuous s).aemeasurable).mp h0)

omit [T2Space A] in
/-- Fubini's theorem along `s`: `∫_A f = c ∫_X ∫_Y f(s⁻¹(x, y)) dy dx`. -/
theorem integral_eq_smul_integral_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : A → E) (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∫ g, f g ∂μ = (splitHaarFactor s μ μX μY : ℝ) • ∫ x, ∫ y, f (s.symm (x, y)) ∂μY ∂μX := by
  have e : ∫ g, f g ∂μ = ∫ p, f (s.symm p) ∂(μ.map s) := by
    have h := integral_map_equiv (μ := μ) s.toHomeomorph.toMeasurableEquiv
      (fun p => f (s.symm p))
    have hc : (⇑s.toHomeomorph.toMeasurableEquiv : A → X × Y) = ⇑s := rfl
    rw [hc] at h
    rw [h]
    simp
  rw [e, map_eq_splitHaarFactor_smul_prod s μ μX μY, integral_smul_nnreal_measure,
    integral_prod, NNReal.smul_def]
  exact (hf.comp s.symm.continuous).integrable_of_hasCompactSupport
    (hfc.comp_homeomorph s.symm.toHomeomorph)

/-- Integral of a product function `f₁(x) f₂(y)` over `A`. -/
theorem integral_mul_split {𝕜 : Type*} [RCLike 𝕜] (f₁ : X → 𝕜) (f₂ : Y → 𝕜)
    (h₁ : Continuous f₁) (h₁c : HasCompactSupport f₁)
    (h₂ : Continuous f₂) (h₂c : HasCompactSupport f₂) :
    ∫ g, f₁ (s g).1 * f₂ (s g).2 ∂μ =
      ((splitHaarFactor s μ μX μY : ℝ) : 𝕜) * ((∫ x, f₁ x ∂μX) * ∫ y, f₂ y ∂μY) := by
  have hc : HasCompactSupport fun g => f₁ (s g).1 * f₂ (s g).2 := by
    refine hasCompactSupport_of_split s _ h₁c h₂c fun g hg => ?_
    refine ⟨subset_tsupport _ ?_, subset_tsupport _ ?_⟩
    · exact left_ne_zero_of_mul hg
    · exact right_ne_zero_of_mul hg
  have hcont : Continuous fun g => f₁ (s g).1 * f₂ (s g).2 :=
    (h₁.comp (continuous_fst.comp (map_continuous s))).mul
      (h₂.comp (continuous_snd.comp (map_continuous s)))
  rw [integral_eq_smul_integral_integral s μ μX μY (fun g => f₁ (s g).1 * f₂ (s g).2) hcont hc]
  simp only [ContinuousMulEquiv.apply_symm_apply]
  simp_rw [integral_const_mul, integral_mul_const]
  rw [RCLike.real_smul_eq_coe_mul]

theorem integral_kernel {b : X → ℂ} (hb : Continuous b) (hbc : HasCompactSupport b)
    {K : Set Y} (hK : IsClopen K) (hKc : IsCompact K) (k : ℂ) :
    ∫ g, kernel s b K k g ∂μ =
      ((splitHaarFactor s μ μX μY : ℝ) : ℂ) * ((k * ∫ x, b x ∂μX) * (μY.real K : ℂ)) := by
  have hKs : HasCompactSupport (K.indicator (1 : Y → ℂ)) :=
    HasCompactSupport.intro hKc fun y hy => Set.indicator_of_notMem hy _
  have h := integral_mul_split s μ μX μY (fun x => k * b x) (K.indicator (1 : Y → ℂ))
    (continuous_const.mul hb) (hbc.mul_left) (hK.continuous_indicator continuous_one) hKs
  rw [integral_const_mul, integral_indicator_one_complex μY hK.isOpen.measurableSet] at h
  exact h

theorem integral_norm_kernel {b : X → ℂ} (hb : Continuous b)
    (hbc : HasCompactSupport b) {K : Set Y} (hK : IsClopen K) (hKc : IsCompact K) (k : ℂ) :
    ∫ g, ‖kernel s b K k g‖ ∂μ =
      (splitHaarFactor s μ μX μY : ℝ) * ((‖k‖ * ∫ x, ‖b x‖ ∂μX) * μY.real K) := by
  have hKs : HasCompactSupport (K.indicator (1 : Y → ℝ)) :=
    HasCompactSupport.intro hKc fun y hy => Set.indicator_of_notMem hy _
  have h := integral_mul_split s μ μX μY (fun x => ‖k‖ * ‖b x‖) (K.indicator (1 : Y → ℝ))
    (continuous_const.mul hb.norm) (hbc.norm.mul_left)
    (hK.continuous_indicator continuous_one) hKs
  rw [integral_const_mul, integral_indicator_one hK.isOpen.measurableSet] at h
  simp_rw [norm_kernel]
  simpa using h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Fubini for the vector-valued integrand: `ρ(kernel) u = c k ∫_X b(x) ρ(x) w dx` with
`w = ∫_Y 1_K(y) ρ(y) u dy`. -/
theorem integral_kernel_smul (ρ : A →* (E →L[ℂ] E))
    (hρ : Langlands.Archimedean.IsContinuousRepresentation ρ) (u : E)
    (ιX : X →* A) (hιX : ∀ x, ιX x = s.symm (x, 1)) (ιY : Y →* A)
    (hιY : ∀ y, ιY y = s.symm (1, y))
    {b : X → ℂ} (hb : Continuous b) (hbc : HasCompactSupport b)
    {K : Set Y} (hK : IsClopen K) (hKc : IsCompact K) (k : ℂ) :
    ∫ g, kernel s b K k g • ρ g u ∂μ =
      (splitHaarFactor s μ μX μY : ℝ) • (k • ∫ x, b x • ρ (ιX x)
        (∫ y, K.indicator (1 : Y → ℂ) y • ρ (ιY y) u ∂μY) ∂μX) := by
  have horb : Continuous fun g => ρ g u := hρ.comp (continuous_id.prodMk continuous_const)
  have hint : Integrable (fun y => K.indicator (1 : Y → ℂ) y • ρ (ιY y) u) μY := by
    refine Continuous.integrable_of_hasCompactSupport
      ((hK.continuous_indicator continuous_one).smul
        (horb.comp (continuous_of_eq_symm_one_left s ιY hιY))) ?_
    exact (HasCompactSupport.intro hKc fun y hy => Set.indicator_of_notMem hy _).smul_right
  rw [integral_eq_smul_integral_integral s μ μX μY (fun g => kernel s b K k g • ρ g u)
    ((continuous_kernel s hb hK k).smul horb) (hasCompactSupport_kernel s hbc hKc k).smul_right]
  congr 1
  rw [← integral_smul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  have hsplit : ∀ y, s.symm (x, y) = ιX x * ιY y := by
    intro y
    rw [hιX, hιY, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  calc ∫ y, kernel s b K k (s.symm (x, y)) • ρ (s.symm (x, y)) u ∂μY
      = ∫ y, (k * b x) • ρ (ιX x) (K.indicator (1 : Y → ℂ) y • ρ (ιY y) u) ∂μY := by
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        dsimp only
        rw [kernel_symm, hsplit, map_mul, mul_apply_eq_comp, map_smul, smul_smul]
    _ = (k * b x) • ρ (ιX x) (∫ y, K.indicator (1 : Y → ℂ) y • ρ (ιY y) u ∂μY) := by
        rw [integral_smul, ContinuousLinearMap.integral_comp_comm _ hint]
    _ = k • (b x • ρ (ιX x) (∫ y, K.indicator (1 : Y → ℂ) y • ρ (ιY y) u ∂μY)) := by
        rw [smul_smul]

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in
/-- The averaged vector is a smooth vector of the restriction of `ρ` to the Lie group `X`. -/
theorem integral_kernel_smul_mem_smoothVectors
    {𝔤 : Type*} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤] [FiniteDimensional ℝ 𝔤]
    [ChartedSpace 𝔤 X] [LieGroup 𝓘(ℝ, 𝔤) ∞ X] [T2Space X]
    (ρ : A →* (E →L[ℂ] E)) (hρ : Langlands.Archimedean.IsContinuousRepresentation ρ) (u : E)
    (ιX : X →* A) (hιX : ∀ x, ιX x = s.symm (x, 1)) (ιY : Y →* A)
    (hιY : ∀ y, ιY y = s.symm (1, y))
    {b : X → ℂ} (hb : ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ b) (hbc : HasCompactSupport b)
    {K : Set Y} (hK : IsClopen K) (hKc : IsCompact K) (k : ℂ) :
    ∫ g, kernel s b K k g • ρ g u ∂μ ∈
      Langlands.Archimedean.smoothVectors 𝓘(ℝ, 𝔤) (ρ.comp ιX) := by
  let : MeasurableSpace X := borel X
  have : BorelSpace X := ⟨rfl⟩
  let : MeasurableSpace Y := borel Y
  have : BorelSpace Y := ⟨rfl⟩
  have hπ : Langlands.Archimedean.IsContinuousRepresentation (ρ.comp ιX) :=
    hρ.comp (((continuous_of_eq_symm_one_right s ιX hιX).comp continuous_fst).prodMk
      continuous_snd)
  rw [integral_kernel_smul s μ (Measure.haar : Measure X) (Measure.haar : Measure Y) ρ hρ u
    ιX hιX ιY hιY hb.continuous hbc hK hKc k]
  refine Submodule.smul_of_tower_mem _ _ (Submodule.smul_mem _ _ ?_)
  exact Langlands.Archimedean.isSmoothVector_gardingIntegral Measure.haar (ρ.comp ιX) hπ b hb
    hbc _

end HaarProduct

section Convergence

variable {A : Type*} [Group A] [TopologicalSpace A]
  [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsHaarMeasure]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Continuous compactly supported kernels `ψ_n` with `∫ ψ_n = 1`, `∫ |ψ_n| = 1` and supports
shrinking to the identity satisfy `ρ(ψ_n) u → u` for every jointly continuous `ρ`. -/
theorem tendsto_integral_smul (ψ : ℕ → A → ℂ) (hψc : ∀ n, Continuous (ψ n))
    (hψs : ∀ n, HasCompactSupport (ψ n)) (h1 : ∀ n, ∫ g, ψ n g ∂μ = 1)
    (hn : ∀ n, ∫ g, ‖ψ n g‖ ∂μ = 1)
    (hsupp : ∀ W ∈ 𝓝 (1 : A), ∀ᶠ n in atTop, ∀ g, ψ n g ≠ 0 → g ∈ W)
    (ρ : A →* (E →L[ℂ] E)) (hρ : Langlands.Archimedean.IsContinuousRepresentation ρ) (u : E) :
    Tendsto (fun n => ∫ g, ψ n g • ρ g u ∂μ) atTop (𝓝 u) := by
  have horb : Continuous fun g => ρ g u := hρ.comp (continuous_id.prodMk continuous_const)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hW : {g : A | ‖ρ g u - u‖ < ε / 2} ∈ 𝓝 (1 : A) := by
    apply IsOpen.mem_nhds
    · exact isOpen_lt (horb.sub continuous_const).norm continuous_const
    · simp [half_pos hε]
  filter_upwards [hsupp _ hW] with n hnW
  have hψint : Integrable (ψ n) μ := (hψc n).integrable_of_hasCompactSupport (hψs n)
  have hint : Integrable (fun g => ψ n g • ρ g u) μ :=
    ((hψc n).smul horb).integrable_of_hasCompactSupport (hψs n).smul_right
  have hint' : Integrable (fun g => ψ n g • u) μ := hψint.smul_const u
  have heq : (∫ g, ψ n g • ρ g u ∂μ) - u = ∫ g, ψ n g • (ρ g u - u) ∂μ := by
    simp_rw [smul_sub]
    rw [integral_sub hint hint', integral_smul_const, h1 n, one_smul]
  rw [dist_eq_norm, heq]
  calc ‖∫ g, ψ n g • (ρ g u - u) ∂μ‖ ≤ ∫ g, ‖ψ n g‖ * (ε / 2) ∂μ := by
        refine norm_integral_le_of_norm_le (hψint.norm.mul_const _) (ae_of_all _ fun g => ?_)
        rw [norm_smul]
        by_cases h : ψ n g = 0
        · simp [h]
        · exact mul_le_mul_of_nonneg_left (hnW g h).le (norm_nonneg _)
    _ = ε / 2 := by rw [integral_mul_const, hn n, one_mul]
    _ < ε := half_lt_self hε

end Convergence

section Assembly

variable {A X Y : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
  [MeasurableSpace A] [BorelSpace A] [T2Space A]
  [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [T2Space X]
  [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [LocallyCompactSpace Y]
  [SecondCountableTopology Y]
  (s : A ≃ₜ* X × Y) (μ : Measure A) [μ.IsHaarMeasure]

/-- Gårding kernels on `A ≃ X × Y`, for a real Lie group `X` and a group `Y` whose identity has
a neighbourhood basis of compact open subgroups. -/
theorem exists_gardingKernels
    {𝔤 : Type*} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤] [FiniteDimensional ℝ 𝔤]
    [ChartedSpace 𝔤 X] [LieGroup 𝓘(ℝ, 𝔤) ∞ X]
    (ιX : X →* A) (hιX : ∀ x, ιX x = s.symm (x, 1)) (ιY : Y →* A)
    (hιY : ∀ y, ιY y = s.symm (1, y))
    (hY : (𝓝 (1 : Y)).HasBasis (fun K : OpenSubgroup Y => IsCompact (K : Set Y))
      (fun K => (K : Set Y))) :
    ∃ ψ : ℕ → A → ℂ,
      (∀ n, Measurable (ψ n) ∧ (∃ C : ℝ, ∀ g, ‖ψ n g‖ ≤ C) ∧ HasCompactSupport (ψ n)) ∧
      ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
        (ρ : A →* (E →L[ℂ] E)), Langlands.Archimedean.IsContinuousRepresentation ρ → ∀ u : E,
        (∀ n, (∫ g, ψ n g • ρ g u ∂μ) ∈
            Langlands.Archimedean.smoothVectors 𝓘(ℝ, 𝔤) (ρ.comp ιX) ∧
          ∃ L : Subgroup Y, IsOpen (L : Set Y) ∧ ∀ l ∈ L,
            ρ (ιY l) (∫ g, ψ n g • ρ g u ∂μ) = ∫ g, ψ n g • ρ g u ∂μ) ∧
        Tendsto (fun n => ∫ g, ψ n g • ρ g u ∂μ) atTop (𝓝 u) := by
  let : MeasurableSpace X := borel X
  have : BorelSpace X := ⟨rfl⟩
  let : MeasurableSpace Y := borel Y
  have : BorelSpace Y := ⟨rfl⟩
  set μX : Measure X := Measure.haar
  set μY : Measure Y := Measure.haar
  obtain ⟨U, hU⟩ := (𝓝 (1 : X)).exists_antitone_basis
  obtain ⟨V, hV⟩ := (𝓝 (1 : Y)).exists_antitone_basis
  have hK : ∀ n, ∃ K : OpenSubgroup Y, IsCompact (K : Set Y) ∧ (K : Set Y) ⊆ V n :=
    fun n => hY.mem_iff.mp (hV.mem n)
  choose K hKc hKV using hK
  have hb : ∀ n, ∃ b : X → ℂ, ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ b ∧ HasCompactSupport b ∧
      tsupport b ⊆ U n ∧ (∫ x, b x ∂μX) = 1 ∧ (∫ x, ‖b x‖ ∂μX) = 1 :=
    fun n => Langlands.Archimedean.exists_normalizedSmoothWeight μX (U n) (hU.mem n)
  choose b hbd hbc hbU hb1 hbn using hb
  set c : ℝ := (splitHaarFactor s μ μX μY : ℝ) with hc_def
  have hc : 0 < c := splitHaarFactor_pos s μ μX μY
  have hKpos : ∀ n, 0 < μY.real (K n) := fun n =>
    ENNReal.toReal_pos ((K n).isOpen.measure_ne_zero μY ⟨1, (K n).one_mem⟩)
      (hKc n).measure_lt_top.ne
  set k : ℕ → ℝ := fun n => (c * μY.real (K n))⁻¹ with hk_def
  have hk : ∀ n, c * (k n * μY.real (K n)) = 1 := fun n => by
    rw [hk_def]
    field_simp [(hKpos n).ne', hc.ne']
  have hkpos : ∀ n, 0 < k n := fun n => inv_pos.mpr (mul_pos hc (hKpos n))
  set ψ : ℕ → A → ℂ := fun n => kernel s (b n) (K n) (k n : ℂ) with hψ_def
  have hψc : ∀ n, Continuous (ψ n) := fun n =>
    continuous_kernel s (hbd n).continuous (K n).isClopen _
  have hψs : ∀ n, HasCompactSupport (ψ n) := fun n => hasCompactSupport_kernel s (hbc n) (hKc n) _
  have hψ1 : ∀ n, ∫ g, ψ n g ∂μ = 1 := fun n => by
    simp only [hψ_def]
    rw [integral_kernel s μ μX μY (hbd n).continuous (hbc n) (K n).isClopen (hKc n), hb1 n,
      mul_one]
    exact_mod_cast hk n
  have hψn : ∀ n, ∫ g, ‖ψ n g‖ ∂μ = 1 := fun n => by
    simp only [hψ_def]
    rw [integral_norm_kernel s μ μX μY (hbd n).continuous (hbc n) (K n).isClopen (hKc n), hbn n,
      mul_one, Complex.norm_real, Real.norm_of_nonneg (hkpos n).le]
    exact hk n
  have hsupp : ∀ W ∈ 𝓝 (1 : A), ∀ᶠ n in atTop, ∀ g, ψ n g ≠ 0 → g ∈ W := fun W hW =>
    eventually_kernel_ne_zero_mem s hU hV b hbU (fun n => (K n : Set Y)) hKV
      (fun n => (k n : ℂ)) hW
  refine ⟨ψ, fun n => ⟨(hψc n).measurable, (hψc n).bounded_above_of_compact_support (hψs n),
    hψs n⟩, ?_⟩
  intro E _ _ _ ρ hρ u
  refine ⟨fun n => ⟨?_, (K n).toSubgroup, (K n).isOpen, fun l hl => ?_⟩,
    tendsto_integral_smul μ ψ hψc hψs hψ1 hψn hsupp ρ hρ u⟩
  · exact integral_kernel_smul_mem_smoothVectors s μ ρ hρ u ιX hιX ιY hιY (hbd n) (hbc n)
      (K n).isClopen (hKc n) _
  · exact integral_kernel_smul_invariant s μ ρ hρ u ιY hιY (hbd n).continuous (hbc n)
      (K n).toSubgroup (K n).isClopen (hKc n) _ hl

end Assembly

end Langlands.Global.AdelicGardingApproximation

namespace Langlands.Global

open scoped CategoryTheory.MonObj
open AdelicGroupPoints

/-- **Gårding smoothing on `G(𝔸)`.** The kernels `ψ_n = c_n · b_n ⊗ 1_{K_n}` on
`G(𝔸) = G(F_∞) × G(𝔸_f)` (along `AdelicGroupPoints.split`), with normalized smooth bumps `b_n` on
`G(F_∞)` and compact open subgroups `K_n` of `G(𝔸_f)` shrinking to the identity, satisfy
`AdelicGardingApproximationStatement`. -/
theorem adelicGardingApproximation : AdelicGardingApproximationStatement := by
  intro F _ _ G _ _ _ _ d hsmooth
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := InfiniteAdelicGroupPoints.smoothChartedSpace F G hsmooth
  have : LieGroup 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d) ∞
      (InfiniteAdelicGroupPoints F G) :=
    InfiniteAdelicGroupPoints.smoothLieGroup F G hsmooth
  exact AdelicGardingApproximation.exists_gardingKernels (split F G) Measure.haar
    (ofInfinite F G).toMonoidHom (fun _ => rfl) (ofFinite F G).toMonoidHom (fun _ => rfl)
    ((finiteAdelicGroupCompactOpenBasis F G).2)

end Langlands.Global
