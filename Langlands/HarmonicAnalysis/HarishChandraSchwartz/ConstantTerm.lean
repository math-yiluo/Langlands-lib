import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Convolution

/-! # The constant term on the Harish-Chandra Schwartz space

Waldspurger 2003, III.6: for a semi-standard parabolic subgroup `P = M U`, `f ∈ C(G)` and
`m ∈ M`, `f^{(P)}(m) = δ_P(m)^{1/2} ∫_U f(m u) du`. By Proposition II.4.5 applied to the
opposite parabolic, the integral converges, `f^{(P)} ∈ C(M)`, and `f ↦ f^{(P)}` is
continuous from `C(G)` to `C(M)`. Here `M` and `U` are subgroups of a topological group
`G` with `M` normalizing `U`, `ν` is a measure on `U`, `δ` is a positive character of `M`,
and the estimate of Proposition II.4.5 is the explicit hypothesis `ConstantTermEstimate`.
-/

noncomputable section

open scoped ENNReal NNReal Topology
open MeasureTheory Filter

namespace Langlands.HarishChandraSchwartz

universe u

section Defs

variable {G : Type u} [Group G] [MeasurableSpace G] {M U : Subgroup G}

/-- Waldspurger's constant term along `P = M U` (III.6):
`f^{(P)}(m) = δ(m)^{1/2} ∫_U f(m u) dν(u)`, for a measure `ν` on `U` and a positive
character `δ` of `M` (Waldspurger's `δ_P` restricted to `M`). -/
def constantTerm (ν : Measure U) (δ : M →* ℝ≥0ˣ) (f : G → ℂ) (m : M) : ℂ :=
  ((NNReal.sqrt (δ m) : ℝ) : ℂ) * ∫ u : U, f ((m : G) * u) ∂ν

/-- The estimate of Proposition II.4.5 of Waldspurger, applied to the opposite parabolic
subgroup `P̄` (whose opposite unipotent radical is `U`): for every `d` there are `d'` and
`c` with `δ(m)^{1/2} ∫_U Ξ(m u) (1 + σ(m u))^{-d'} dν(u) ≤ c Ξ^M(m) (1 + σ^M(m))^{-d}` for
all `m ∈ M`. Here `Ξ^M` and `σ^M` are the weights of `C(M)`. -/
def ConstantTermEstimate (ν : Measure U) (δ : M →* ℝ≥0ˣ) (Ξ σ : G → ℝ) (ΞM σM : M → ℝ) :
    Prop :=
  ∀ d : ℝ, ∃ d' : ℝ, ∃ c : ℝ≥0, ∀ m : M,
    (NNReal.sqrt (δ m) : ℝ≥0∞) *
        ∫⁻ u : U, ENNReal.ofReal (Ξ ((m : G) * u) * (1 + σ ((m : G) * u)) ^ (-d')) ∂ν ≤
      c * ENNReal.ofReal (ΞM m * (1 + σM m) ^ (-d))

variable (ν : Measure U) (δ : M →* ℝ≥0ˣ)

theorem constantTerm_smul (c : ℂ) (f : G → ℂ) :
    constantTerm ν δ (c • f) = c • constantTerm ν δ f := by
  funext m
  simp only [constantTerm, Pi.smul_apply, smul_eq_mul, integral_const_mul]
  ring

variable {ν δ} in
theorem constantTerm_add {f₁ f₂ : G → ℂ}
    (h₁ : ∀ m : M, Integrable (fun u : U => f₁ ((m : G) * u)) ν)
    (h₂ : ∀ m : M, Integrable (fun u : U => f₂ ((m : G) * u)) ν) :
    constantTerm ν δ (f₁ + f₂) = constantTerm ν δ f₁ + constantTerm ν δ f₂ := by
  funext m
  simp only [constantTerm, Pi.add_apply, integral_add (h₁ m) (h₂ m)]
  ring

theorem enorm_constantTerm_le (f : G → ℂ) (m : M) :
    ‖constantTerm ν δ f m‖ₑ ≤
      (NNReal.sqrt (δ m) : ℝ≥0∞) * ∫⁻ u : U, ‖f ((m : G) * u)‖ₑ ∂ν := by
  rw [constantTerm, enorm_mul]
  gcongr
  · rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _),
      ENNReal.ofReal_coe_nnreal]
  · exact enorm_integral_le_lintegral_enorm _

end Defs

section Estimates

variable {G : Type u} [Group G] [MeasurableSpace G] {M U : Subgroup G}
  {ν : Measure U} {δ : M →* ℝ≥0ˣ} {Ξ σ : G → ℝ} {ΞM σM : M → ℝ}

/-- The seminorm estimate `ν^M_d(f^{(P)}) ≤ c ν_{d'}(f)` (from the estimate of
Proposition II.4.5). -/
theorem ConstantTermEstimate.nu_le (h : ConstantTermEstimate ν δ Ξ σ ΞM σM)
    (hΞ : ∀ g, 0 < Ξ g) (hσ : ∀ g, 0 ≤ σ g) (hΞM : ∀ m, 0 < ΞM m) (hσM : ∀ m, 0 ≤ σM m)
    (d : ℝ) : ∃ d' : ℝ, ∃ c : ℝ≥0, ∀ f : G → ℂ, nu Ξ σ d' f ≠ ⊤ →
      nu ΞM σM d (constantTerm ν δ f) ≤ c * nu Ξ σ d' f := by
  obtain ⟨d', c, hc⟩ := h d
  refine ⟨d', c, fun f hf => iSup_le fun m => ?_⟩
  have h1 : ‖constantTerm ν δ f m‖ₑ ≤
      nu Ξ σ d' f * (c * ENNReal.ofReal (ΞM m * (1 + σM m) ^ (-d))) := by
    calc ‖constantTerm ν δ f m‖ₑ
        ≤ (NNReal.sqrt (δ m) : ℝ≥0∞) * ∫⁻ u : U, ‖f ((m : G) * u)‖ₑ ∂ν :=
          enorm_constantTerm_le ν δ f m
      _ ≤ (NNReal.sqrt (δ m) : ℝ≥0∞) * ∫⁻ u : U, nu Ξ σ d' f *
            ENNReal.ofReal (Ξ ((m : G) * u) * (1 + σ ((m : G) * u)) ^ (-d')) ∂ν := by
          gcongr with u
          exact enorm_le_nu_mul hΞ hσ f d' _
      _ = nu Ξ σ d' f * ((NNReal.sqrt (δ m) : ℝ≥0∞) * ∫⁻ u : U,
            ENNReal.ofReal (Ξ ((m : G) * u) * (1 + σ ((m : G) * u)) ^ (-d')) ∂ν) := by
          rw [lintegral_const_mul' _ _ hf]
          ring
      _ ≤ nu Ξ σ d' f * (c * ENNReal.ofReal (ΞM m * (1 + σM m) ^ (-d))) := by
          exact mul_le_mul_of_nonneg_left (hc m) zero_le
  calc ‖constantTerm ν δ f m‖ₑ * weight ΞM σM d m
      ≤ nu Ξ σ d' f * (c * ENNReal.ofReal (ΞM m * (1 + σM m) ^ (-d))) *
          weight ΞM σM d m := by gcongr
    _ = c * nu Ξ σ d' f * (weight ΞM σM d m * ENNReal.ofReal (ΞM m * (1 + σM m) ^ (-d))) := by
          ring
    _ = c * nu Ξ σ d' f := by rw [weight_mul_ofReal hΞM hσM, mul_one]

end Estimates

section Restriction

variable {G : Type u} [Group G] [TopologicalSpace G] {M U : Subgroup G}

/-- The conjugation `u ↦ m u m⁻¹` of `U` by an element `m` of a subgroup normalizing `U`. -/
def conjUnipotent (hMU : M ≤ Subgroup.normalizer (U : Set G)) (m : M) : U → U :=
  fun u => ⟨(m : G) * u * (m : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hMU m.2) u).mp u.2⟩

theorem continuous_conjUnipotent [ContinuousMul G] (hMU : M ≤ Subgroup.normalizer (U : Set G)) (m : M) :
    Continuous (conjUnipotent hMU m) :=
  ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

/-- The compact open subgroup `H ∩ M` of a closed subgroup `M`. -/
def CompactOpenSubgroup.subgroupOf (hM : IsClosed (M : Set G)) (H : CompactOpenSubgroup G) :
    CompactOpenSubgroup M :=
  ⟨H.1.comap M.subtype continuous_subtype_val,
    hM.isClosedEmbedding_subtypeVal.isCompact_preimage H.2⟩

theorem CompactOpenSubgroup.mem_subgroupOf {hM : IsClosed (M : Set G)}
    {H : CompactOpenSubgroup G} {m : M} :
    m ∈ (H.subgroupOf hM).toSubgroup ↔ (m : G) ∈ H.toSubgroup :=
  Iff.rfl

end Restriction

section Topological

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] {M U : Subgroup G}
  {ν : Measure U} {δ : M →* ℝ≥0ˣ} {Ξ σ : G → ℝ} {ΞM σM : M → ℝ}

/-- For `f` continuous with `ν_r(f)` finite for all `r`, the integrand `u ↦ f(m u)` of the
constant term is integrable (convergence assertion of III.6). -/
theorem ConstantTermEstimate.integrable (h : ConstantTermEstimate ν δ Ξ σ ΞM σM)
    (hΞ : ∀ g, 0 < Ξ g) (hσ : ∀ g, 0 ≤ σ g) {f : G → ℂ} (hfc : Continuous f)
    (hf : ∀ r, nu Ξ σ r f < ⊤) (m : M) :
    Integrable (fun u : U => f ((m : G) * u)) ν := by
  obtain ⟨d', c, hc⟩ := h 0
  refine ⟨(hfc.comp (continuous_const.mul continuous_subtype_val)).aestronglyMeasurable, ?_⟩
  have hsq : (NNReal.sqrt (δ m) : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, ENNReal.coe_eq_zero, NNReal.sqrt_eq_zero]
    exact (δ m).ne_zero
  have hI : ∫⁻ u : U, ENNReal.ofReal (Ξ ((m : G) * u) * (1 + σ ((m : G) * u)) ^ (-d')) ∂ν
      < ⊤ := by
    have h1 := (hc m).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.ofReal_lt_top)
    exact ENNReal.lt_top_of_mul_ne_top_right h1.ne hsq
  calc ∫⁻ u : U, ‖f ((m : G) * u)‖ₑ ∂ν
      ≤ ∫⁻ u : U, nu Ξ σ d' f *
          ENNReal.ofReal (Ξ ((m : G) * u) * (1 + σ ((m : G) * u)) ^ (-d')) ∂ν := by
        gcongr with u
        exact enorm_le_nu_mul hΞ hσ f d' _
    _ = nu Ξ σ d' f * ∫⁻ u : U,
          ENNReal.ofReal (Ξ ((m : G) * u) * (1 + σ ((m : G) * u)) ^ (-d')) ∂ν :=
        lintegral_const_mul' _ _ (hf d').ne
    _ < ⊤ := ENNReal.mul_lt_top (hf d') hI

/-- The hypotheses on `M`, `U`, `ν` and `δ` under which the constant term maps the level
`C_H` of `G` to the level `C_{H ∩ M}` of `M`, for every compact open subgroup `H` of `G`:
`M` is closed and normalizes `U`, and for `m ∈ M ∩ H` the character `δ` is trivial at `m`
and `ν` is invariant under conjugation by `m`. For Waldspurger's `P = M U`, `ν` a Haar
measure on `U` and `δ = δ_P`, both hold because `M ∩ H` is compact. -/
structure ConstantTermData (ν : Measure U) (δ : M →* ℝ≥0ˣ) : Prop where
  isClosed : IsClosed (M : Set G)
  le_normalizer : M ≤ Subgroup.normalizer (U : Set G)
  delta_eq_one : ∀ H : CompactOpenSubgroup G, ∀ m : M, (m : G) ∈ H.toSubgroup → δ m = 1
  map_conj : ∀ H : CompactOpenSubgroup G, ∀ m : M, (m : G) ∈ H.toSubgroup →
    ν.map (conjUnipotent le_normalizer m) = ν

/-- If `f` is bi-invariant under `H`, then `f^{(P)}` is bi-invariant under `H ∩ M`. -/
theorem ConstantTermData.isBiInvariant (hD : ConstantTermData ν δ) {H : CompactOpenSubgroup G}
    {f : G → ℂ} (hfc : Continuous f) (hf : IsBiInvariant H.toSubgroup f) :
    IsBiInvariant (H.subgroupOf hD.isClosed).toSubgroup (constantTerm ν δ f) := by
  intro k₁ hk₁ k₂ hk₂ m
  have hk₁' : (k₁ : G) ∈ H.toSubgroup := hk₁
  have hk₂' : (k₂ : G) ∈ H.toSubgroup := hk₂
  simp only [constantTerm]
  rw [map_mul, map_mul, hD.delta_eq_one H k₁ hk₁', hD.delta_eq_one H k₂ hk₂', one_mul, mul_one]
  congr 1
  have hconj := hD.map_conj H k₂ hk₂'
  have hφ : Continuous fun u : U => f ((m : G) * u) :=
    hfc.comp (continuous_const.mul continuous_subtype_val)
  calc ∫ u : U, f (((k₁ * m * k₂ : M) : G) * u) ∂ν
      = ∫ u : U, f ((m : G) * (conjUnipotent hD.le_normalizer k₂ u)) ∂ν := by
        congr 1
        funext u
        have : ((k₁ * m * k₂ : M) : G) * u =
            (k₁ : G) * ((m : G) * (conjUnipotent hD.le_normalizer k₂ u)) * (k₂ : G) := by
          simp only [conjUnipotent, Subgroup.coe_mul]
          group
        rw [this, hf _ hk₁' _ hk₂']
    _ = ∫ u : U, f ((m : G) * u) ∂(ν.map (conjUnipotent hD.le_normalizer k₂)) :=
        (integral_map (continuous_conjUnipotent _ _).measurable.aemeasurable
          hφ.aestronglyMeasurable).symm
    _ = ∫ u : U, f ((m : G) * u) ∂ν := by rw [hconj]

/-- Waldspurger III.6: for `f ∈ C_H`, the constant term `f^{(P)}` lies in the level
`C_{H ∩ M}` of `C(M)`. -/
theorem ConstantTermData.constantTerm_mem_levelSubmodule (hD : ConstantTermData ν δ)
    (h : ConstantTermEstimate ν δ Ξ σ ΞM σM) (hΞ : ∀ g, 0 < Ξ g) (hσ : ∀ g, 0 ≤ σ g)
    (hΞM : ∀ m, 0 < ΞM m) (hσM : ∀ m, 0 ≤ σM m) {H : CompactOpenSubgroup G} {f : G → ℂ}
    (hf : f ∈ levelSubmodule Ξ σ H.toSubgroup) :
    constantTerm ν δ f ∈ levelSubmodule ΞM σM (H.subgroupOf hD.isClosed).toSubgroup := by
  refine ⟨hD.isBiInvariant (continuous_of_mem_levelSubmodule hf) hf.1, fun r => ?_⟩
  obtain ⟨d', c, hc⟩ := h.nu_le hΞ hσ hΞM hσM r
  exact (hc f (hf.2 d').ne).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top (hf.2 d'))

namespace Level

/-- The constant term as a linear map from the level `C_H` of `G` to the level `C_{H ∩ M}`
of `M`. -/
def constantTerm (hD : ConstantTermData ν δ) (h : ConstantTermEstimate ν δ Ξ σ ΞM σM)
    (hΞ : ∀ g, 0 < Ξ g) (hσ : ∀ g, 0 ≤ σ g) (hΞM : ∀ m, 0 < ΞM m) (hσM : ∀ m, 0 ≤ σM m)
    (H : CompactOpenSubgroup G) :
    Level Ξ σ H →ₗ[ℂ] Level ΞM σM (H.subgroupOf hD.isClosed) where
  toFun f := (⟨HarishChandraSchwartz.constantTerm ν δ f,
    hD.constantTerm_mem_levelSubmodule h hΞ hσ hΞM hσM
      (f : levelSubmodule Ξ σ H.toSubgroup).2⟩ :
    levelSubmodule ΞM σM (H.subgroupOf hD.isClosed).toSubgroup)
  map_add' f f' := Level.ext fun m => congrFun (constantTerm_add (δ := δ)
      (h.integrable hΞ hσ (continuous_of_mem_levelSubmodule
        (f : levelSubmodule Ξ σ H.toSubgroup).2) (f : levelSubmodule Ξ σ H.toSubgroup).2.2)
      (h.integrable hΞ hσ (continuous_of_mem_levelSubmodule
        (f' : levelSubmodule Ξ σ H.toSubgroup).2) (f' : levelSubmodule Ξ σ H.toSubgroup).2.2))
      m
  map_smul' c f := Level.ext fun m => congrFun (constantTerm_smul ν δ c f) m

@[simp] theorem coe_constantTerm (hD : ConstantTermData ν δ)
    (h : ConstantTermEstimate ν δ Ξ σ ΞM σM) (hΞ : ∀ g, 0 < Ξ g) (hσ : ∀ g, 0 ≤ σ g)
    (hΞM : ∀ m, 0 < ΞM m) (hσM : ∀ m, 0 ≤ σM m) (H : CompactOpenSubgroup G)
    (f : Level Ξ σ H) :
    ((constantTerm hD h hΞ hσ hΞM hσM H f : Level ΞM σM (H.subgroupOf hD.isClosed)) :
      M → ℂ) = HarishChandraSchwartz.constantTerm ν δ f :=
  rfl

/-- Waldspurger III.6: the constant term is continuous from `C_H` to `C_{H ∩ M}`. -/
theorem continuous_constantTerm (hD : ConstantTermData ν δ)
    (h : ConstantTermEstimate ν δ Ξ σ ΞM σM) (hΞ : ∀ g, 0 < Ξ g) (hσ : ∀ g, 0 ≤ σ g)
    (hΞM : ∀ m, 0 < ΞM m) (hσM : ∀ m, 0 ≤ σM m) (H : CompactOpenSubgroup G) :
    Continuous (constantTerm hD h hΞ hσ hΞM hσM H) := by
  refine (withSeminorms H).continuous_of_isBounded
    (withSeminorms (H.subgroupOf hD.isClosed)) _ ?_
  refine Seminorm.IsBounded.of_real fun r => ?_
  obtain ⟨d', c, hc⟩ := h.nu_le hΞ hσ hΞM hσM r
  refine ⟨{d'}, (c : ℝ), fun f => ?_⟩
  rw [Finset.sup_singleton]
  change (nu ΞM σM r (HarishChandraSchwartz.constantTerm ν δ f)).toReal ≤
    (c : ℝ) * (nu Ξ σ d' f).toReal
  rw [← ENNReal.coe_toReal c, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top (nu_ne_top f d'))
    (hc f (nu_ne_top f d'))

end Level

variable [Nonempty (CompactOpenSubgroup G)]

/-- For `f ∈ C(G)`, the integrand `u ↦ f(m u)` of the constant term is integrable. -/
theorem ConstantTermEstimate.integrable_of_mem_schwartzSubmodule
    (h : ConstantTermEstimate ν δ Ξ σ ΞM σM) (hΞ : ∀ g, 0 < Ξ g) (hσ : ∀ g, 0 ≤ σ g)
    {f : G → ℂ} (hf : f ∈ schwartzSubmodule Ξ σ) (m : M) :
    Integrable (fun u : U => f ((m : G) * u)) ν := by
  obtain ⟨H, hH⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp hf
  exact h.integrable hΞ hσ (continuous_of_mem_levelSubmodule hH) hH.2 m

/-- Waldspurger III.6: `f^{(P)} ∈ C(M)` for `f ∈ C(G)`. -/
theorem ConstantTermData.constantTerm_mem_schwartzSubmodule (hD : ConstantTermData ν δ)
    (h : ConstantTermEstimate ν δ Ξ σ ΞM σM) (hΞ : ∀ g, 0 < Ξ g) (hσ : ∀ g, 0 ≤ σ g)
    (hΞM : ∀ m, 0 < ΞM m) (hσM : ∀ m, 0 ≤ σM m) {f : G → ℂ}
    (hf : f ∈ schwartzSubmodule Ξ σ) :
    constantTerm ν δ f ∈ schwartzSubmodule ΞM σM := by
  obtain ⟨H, hH⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp hf
  exact levelSubmodule_le_schwartzSubmodule ΞM σM (H.subgroupOf hD.isClosed)
    (hD.constantTerm_mem_levelSubmodule h hΞ hσ hΞM hσM hH)

namespace Space

/-- The constant term `C(G) → C(M)`, `f ↦ f^{(P)}`, as a linear map. -/
def constantTermLinear (hD : ConstantTermData ν δ) (h : ConstantTermEstimate ν δ Ξ σ ΞM σM)
    (hΞ : ∀ g, 0 < Ξ g) (hσ : ∀ g, 0 ≤ σ g) (hΞM : ∀ m, 0 < ΞM m) (hσM : ∀ m, 0 ≤ σM m) :
    Space Ξ σ →ₗ[ℂ] Space ΞM σM where
  toFun f := (⟨HarishChandraSchwartz.constantTerm ν δ f,
    hD.constantTerm_mem_schwartzSubmodule h hΞ hσ hΞM hσM (coe_mem f)⟩ :
    schwartzSubmodule ΞM σM)
  map_add' f f' := ext fun m => congrFun (constantTerm_add (δ := δ)
      (h.integrable_of_mem_schwartzSubmodule hΞ hσ (coe_mem f))
      (h.integrable_of_mem_schwartzSubmodule hΞ hσ (coe_mem f'))) m
  map_smul' c f := ext fun m => congrFun (constantTerm_smul ν δ c f) m

/-- Waldspurger III.6: the constant term `C(G) → C(M)`, `f ↦ f^{(P)}`, as a continuous
linear map. -/
def constantTerm (hD : ConstantTermData ν δ) (h : ConstantTermEstimate ν δ Ξ σ ΞM σM)
    (hΞ : ∀ g, 0 < Ξ g) (hσ : ∀ g, 0 ≤ σ g) (hΞM : ∀ m, 0 < ΞM m) (hσM : ∀ m, 0 ≤ σM m) :
    Space Ξ σ →L[ℂ] Space ΞM σM :=
  mkCLM (constantTermLinear hD h hΞ hσ hΞM hσM) fun H => by
    have e : (constantTermLinear hD h hΞ hσ hΞM hσM ∘ ofLevel H :
        Level Ξ σ H → Space ΞM σM) =
        ofLevel (H.subgroupOf hD.isClosed) ∘ Level.constantTerm hD h hΞ hσ hΞM hσM H :=
      funext fun _ => ext fun _ => rfl
    rw [e]
    exact (continuous_ofLevel _).comp (Level.continuous_constantTerm hD h hΞ hσ hΞM hσM H)

@[simp] theorem coe_constantTerm (hD : ConstantTermData ν δ)
    (h : ConstantTermEstimate ν δ Ξ σ ΞM σM) (hΞ : ∀ g, 0 < Ξ g) (hσ : ∀ g, 0 ≤ σ g)
    (hΞM : ∀ m, 0 < ΞM m) (hσM : ∀ m, 0 ≤ σM m) (f : Space Ξ σ) :
    ((constantTerm hD h hΞ hσ hΞM hσM f : Space ΞM σM) : M → ℂ) =
      HarishChandraSchwartz.constantTerm ν δ f :=
  rfl

end Space


end Topological

end Langlands.HarishChandraSchwartz
