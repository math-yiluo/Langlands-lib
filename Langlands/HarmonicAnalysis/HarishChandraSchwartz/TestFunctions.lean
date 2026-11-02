import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Basic
import Langlands.Representation.Hecke.CommonInvarianceProof

/-! # Test functions in the Harish-Chandra Schwartz space

Waldspurger 2003, III.6: `C_c^∞(G)` is contained and dense in `C(G)`. Here the weights
`Ξ` and `σ` are arbitrary; the properties of the source weights used by the argument
are explicit hypotheses.
-/

noncomputable section

open scoped ENNReal NNReal Topology
open Filter

namespace Langlands.HarishChandraSchwartz

universe u

open HarmonicAnalysis (SchwartzBruhat schwartzBruhatSubmodule)

section Bounds

variable {G : Type u} [TopologicalSpace G] {Ξ σ : G → ℝ}

/-- For continuous positive `Ξ` and continuous nonnegative `σ`, every continuous compactly
supported function has finite `ν_r` for every `r`. -/
theorem nu_lt_top_of_hasCompactSupport (hΞc : Continuous Ξ) (hΞ : ∀ g, 0 < Ξ g)
    (hσc : Continuous σ) (hσ : ∀ g, 0 ≤ σ g) {f : G → ℂ} (hf : Continuous f)
    (hfs : HasCompactSupport f) (r : ℝ) : nu Ξ σ r f < ⊤ := by
  set w : G → ℝ := fun g => (Ξ g)⁻¹ * (1 + σ g) ^ r with hw_def
  have hw : Continuous w :=
    (hΞc.inv₀ fun g => (hΞ g).ne').mul
      ((continuous_const.add hσc).rpow_const fun g =>
        Or.inl (ne_of_gt (show 0 < 1 + σ g by linarith [hσ g])))
  have hF : Continuous fun g => ‖f g‖ * w g := hf.norm.mul hw
  have hFs : HasCompactSupport fun g => ‖f g‖ * w g :=
    HasCompactSupport.mul_right (f := fun g => ‖f g‖) hfs.norm
  obtain ⟨C, hC⟩ := hF.bounded_above_of_compact_support hFs
  have hle : nu Ξ σ r f ≤ ENNReal.ofReal C := by
    refine iSup_le fun g => ?_
    have hwg : 0 ≤ w g :=
      (mul_pos (inv_pos.mpr (hΞ g)) (Real.rpow_pos_of_pos (by linarith [hσ g]) r)).le
    rw [weight, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := hC g
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) hwg)] at h
    exact h
  exact lt_of_le_of_lt hle ENNReal.ofReal_lt_top

end Bounds

section Truncation

variable {G : Type u} [Group G] {Ξ σ : G → ℝ}

/-- The truncation `f · 1_{σ ≤ N}` of a function `f` along the weight `σ`. -/
def truncate (σ : G → ℝ) (N : ℝ) (f : G → ℂ) : G → ℂ :=
  {g | σ g ≤ N}.indicator f

omit [Group G] in
theorem truncate_apply_of_le {N : ℝ} {f : G → ℂ} {g : G} (hg : σ g ≤ N) :
    truncate σ N f g = f g :=
  Set.indicator_of_mem (s := {g | σ g ≤ N}) hg f

omit [Group G] in
theorem truncate_apply_of_lt {N : ℝ} {f : G → ℂ} {g : G} (hg : N < σ g) :
    truncate σ N f g = 0 :=
  Set.indicator_of_notMem (s := {g | σ g ≤ N}) (not_le.mpr hg) f

/-- A truncation of an `H`-bi-invariant function along an `H`-bi-invariant `σ` is
`H`-bi-invariant. -/
theorem IsBiInvariant.truncate {H : Subgroup G} {f : G → ℂ} (hf : IsBiInvariant H f)
    (hσH : ∀ h₁ ∈ H, ∀ h₂ ∈ H, ∀ g, σ (h₁ * g * h₂) = σ g) (N : ℝ) :
    IsBiInvariant H (truncate σ N f) := by
  intro h₁ h₁m h₂ h₂m g
  unfold HarishChandraSchwartz.truncate
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, hσH h₁ h₁m h₂ h₂m g, hf h₁ h₁m h₂ h₂m g]

omit [Group G] in
theorem nu_truncate_le (N r : ℝ) (f : G → ℂ) : nu Ξ σ r (truncate σ N f) ≤ nu Ξ σ r f := by
  refine iSup_mono fun g => ?_
  by_cases hg : σ g ≤ N
  · rw [truncate_apply_of_le hg]
  · rw [truncate_apply_of_lt (not_le.mp hg), enorm_zero, zero_mul]
    exact zero_le

omit [Group G] in
/-- The tail estimate behind the density of test functions: for positive `Ξ` and
`0 ≤ N`, `ν_r(f - f · 1_{σ ≤ N}) ≤ (1 + N)⁻¹ ν_{r+1}(f)`. -/
theorem nu_sub_truncate_le (hΞ : ∀ g, 0 < Ξ g) {N : ℝ} (hN : 0 ≤ N) (r : ℝ) (f : G → ℂ) :
    nu Ξ σ r (f - truncate σ N f) ≤ ENNReal.ofReal (1 + N)⁻¹ * nu Ξ σ (r + 1) f := by
  refine iSup_le fun g => ?_
  by_cases hg : σ g ≤ N
  · rw [Pi.sub_apply, truncate_apply_of_le hg, sub_self, enorm_zero, zero_mul]
    exact zero_le
  · have hlt : N < σ g := not_le.mp hg
    rw [Pi.sub_apply, truncate_apply_of_lt hlt, sub_zero]
    have hN1 : 0 < 1 + N := by linarith
    have hσ1 : 0 < 1 + σ g := by linarith
    have hw : weight Ξ σ r g ≤ ENNReal.ofReal (1 + N)⁻¹ * weight Ξ σ (r + 1) g := by
      unfold weight
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hN1.le)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [Real.rpow_add_one hσ1.ne']
      have hpos : 0 ≤ (Ξ g)⁻¹ * (1 + σ g) ^ r :=
        (mul_pos (inv_pos.mpr (hΞ g)) (Real.rpow_pos_of_pos hσ1 r)).le
      have hratio : 1 ≤ (1 + N)⁻¹ * (1 + σ g) := by
        rw [inv_mul_eq_div, one_le_div hN1]
        linarith
      calc (Ξ g)⁻¹ * (1 + σ g) ^ r = (Ξ g)⁻¹ * (1 + σ g) ^ r * 1 := (mul_one _).symm
        _ ≤ (Ξ g)⁻¹ * (1 + σ g) ^ r * ((1 + N)⁻¹ * (1 + σ g)) :=
            mul_le_mul_of_nonneg_left hratio hpos
        _ = (1 + N)⁻¹ * ((Ξ g)⁻¹ * ((1 + σ g) ^ r * (1 + σ g))) := by ring
    calc ‖f g‖ₑ * weight Ξ σ r g
        ≤ ‖f g‖ₑ * (ENNReal.ofReal (1 + N)⁻¹ * weight Ξ σ (r + 1) g) := by gcongr
      _ = ENNReal.ofReal (1 + N)⁻¹ * (‖f g‖ₑ * weight Ξ σ (r + 1) g) := by ring
      _ ≤ ENNReal.ofReal (1 + N)⁻¹ * nu Ξ σ (r + 1) f := by
          gcongr
          exact enorm_mul_weight_le_nu f g

end Truncation

section TopologicalGroup

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A function bi-invariant under a compact open subgroup is locally constant. -/
theorem IsBiInvariant.isLocallyConstant {K : CompactOpenSubgroup G} {f : G → ℂ}
    (hf : IsBiInvariant K.toSubgroup f) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hopen : IsOpen {y : G | x⁻¹ * y ∈ (K.1 : Set G)} :=
    K.1.isOpen.preimage (continuous_const.mul continuous_id)
  have hx : x ∈ {y : G | x⁻¹ * y ∈ (K.1 : Set G)} := by
    simp only [Set.mem_ofPred_eq, inv_mul_cancel]
    exact K.1.one_mem
  filter_upwards [hopen.mem_nhds hx] with y hy
  have h := hf 1 K.toSubgroup.one_mem (x⁻¹ * y) hy x
  simpa [mul_assoc] using h

variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

/-- Every test function is bi-invariant under some compact open subgroup contained in a
prescribed open subgroup. -/
theorem exists_isBiInvariant_schwartzBruhat (f : SchwartzBruhat G) (U : OpenSubgroup G) :
    ∃ K : CompactOpenSubgroup G, K.1 ≤ U ∧ IsBiInvariant K.toSubgroup f := by
  obtain ⟨K, hKU, hKc, hK⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance.{u} G {f} U
  refine ⟨⟨K, hKc⟩, hKU, fun h₁ h₁m h₂ h₂m g => ?_⟩
  have hf := hK f (Finset.mem_singleton_self f)
  rw [hf.2 ⟨h₂, h₂m⟩ (h₁ * g), hf.1 ⟨h₁, h₁m⟩ g]

variable {Ξ σ : G → ℝ}

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] in
/-- For continuous positive `Ξ` and continuous nonnegative `σ`, every test function lies in
the level of any compact open subgroup under which it is bi-invariant. -/
theorem schwartzBruhat_mem_levelSubmodule (hΞc : Continuous Ξ) (hΞ : ∀ g, 0 < Ξ g)
    (hσc : Continuous σ) (hσ : ∀ g, 0 ≤ σ g) (f : SchwartzBruhat G) {K : CompactOpenSubgroup G}
    (hK : IsBiInvariant K.toSubgroup f) :
    (f : G → ℂ) ∈ levelSubmodule Ξ σ K.toSubgroup :=
  ⟨hK, nu_lt_top_of_hasCompactSupport hΞc hΞ hσc hσ (HarmonicAnalysis.SchwartzBruhat.continuous f)
    (HarmonicAnalysis.SchwartzBruhat.hasCompactSupport f)⟩

/-- Waldspurger III.6: `C_c^∞(G) ⊆ C(G)`, for continuous positive `Ξ` and continuous
nonnegative `σ`. -/
theorem schwartzBruhat_mem_schwartzSubmodule (hΞc : Continuous Ξ) (hΞ : ∀ g, 0 < Ξ g)
    (hσc : Continuous σ) (hσ : ∀ g, 0 ≤ σ g) (f : SchwartzBruhat G) :
    (f : G → ℂ) ∈ schwartzSubmodule Ξ σ := by
  obtain ⟨K, -, hK⟩ := exists_isBiInvariant_schwartzBruhat f ⊤
  exact levelSubmodule_le_schwartzSubmodule Ξ σ K
    (schwartzBruhat_mem_levelSubmodule hΞc hΞ hσc hσ f hK)

/-- The inclusion `C_c^∞(G) → C(G)` as a linear map. -/
def ofSchwartzBruhat (hΞc : Continuous Ξ) (hΞ : ∀ g, 0 < Ξ g) (hσc : Continuous σ)
    (hσ : ∀ g, 0 ≤ σ g) : SchwartzBruhat G →ₗ[ℂ] Space Ξ σ where
  toFun f := (⟨(f : G → ℂ), schwartzBruhat_mem_schwartzSubmodule hΞc hΞ hσc hσ f⟩ :
    schwartzSubmodule Ξ σ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coe_ofSchwartzBruhat (hΞc : Continuous Ξ) (hΞ : ∀ g, 0 < Ξ g)
    (hσc : Continuous σ) (hσ : ∀ g, 0 ≤ σ g) (f : SchwartzBruhat G) :
    ((ofSchwartzBruhat hΞc hΞ hσc hσ f : Space Ξ σ) : G → ℂ) = f :=
  rfl

theorem ofSchwartzBruhat_injective (hΞc : Continuous Ξ) (hΞ : ∀ g, 0 < Ξ g)
    (hσc : Continuous σ) (hσ : ∀ g, 0 ≤ σ g) :
    Function.Injective (ofSchwartzBruhat hΞc hΞ hσc hσ) := fun _ _ h =>
  Subtype.ext (congrArg (fun f : Space Ξ σ => (f : G → ℂ)) h)

/-- The truncation `f · 1_{σ ≤ N}` of an element of a level is a test function, provided
`σ` is bi-invariant under a compact open subgroup and has compact sublevel sets. -/
def truncateSchwartzBruhat (K₀ : CompactOpenSubgroup G)
    (hσK : ∀ k₁ ∈ K₀.toSubgroup, ∀ k₂ ∈ K₀.toSubgroup, ∀ g, σ (k₁ * g * k₂) = σ g)
    (hσN : ∀ N : ℝ, IsCompact {g | σ g ≤ N}) {K : CompactOpenSubgroup G} {f : G → ℂ}
    (hf : IsBiInvariant K.toSubgroup f) (N : ℝ) : SchwartzBruhat G :=
  ⟨truncate σ N f,
    (IsBiInvariant.truncate (hf.mono (K.inf_le_left K₀))
      (fun h₁ h₁m h₂ h₂m g => hσK h₁ (K.inf_le_right K₀ h₁m) h₂ (K.inf_le_right K₀ h₂m) g)
      N).isLocallyConstant (K := K.inf K₀),
    HasCompactSupport.intro' (hσN N) (hσN N).isClosed fun _ hg =>
      truncate_apply_of_lt (not_le.mp hg)⟩

/-- Waldspurger III.6: `C_c^∞(G)` is dense in `C(G)`. The hypotheses on the weights are
those used by the truncation argument: `Ξ` continuous and positive, and `σ` continuous,
nonnegative, bi-invariant under a compact open subgroup `K₀`, with compact sublevel sets
`{σ ≤ N}`. -/
theorem denseRange_ofSchwartzBruhat (hΞc : Continuous Ξ) (hΞ : ∀ g, 0 < Ξ g)
    (hσc : Continuous σ) (hσ : ∀ g, 0 ≤ σ g) (K₀ : CompactOpenSubgroup G)
    (hσK : ∀ k₁ ∈ K₀.toSubgroup, ∀ k₂ ∈ K₀.toSubgroup, ∀ g, σ (k₁ * g * k₂) = σ g)
    (hσN : ∀ N : ℝ, IsCompact {g | σ g ≤ N}) :
    DenseRange (ofSchwartzBruhat hΞc hΞ hσc hσ) := by
  intro F
  have : Nonempty (CompactOpenSubgroup G) := ⟨K₀⟩
  obtain ⟨K, hFK⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp (Space.coe_mem F)
  set L := K.inf K₀ with hL
  have hFL : (F : G → ℂ) ∈ levelSubmodule Ξ σ L.toSubgroup :=
    levelSubmodule_antitone Ξ σ (K.inf_le_left K₀) hFK
  let fL : Level Ξ σ L := (⟨(F : G → ℂ), hFL⟩ : levelSubmodule Ξ σ L.toSubgroup)
  have hσL : ∀ h₁ ∈ L.toSubgroup, ∀ h₂ ∈ L.toSubgroup, ∀ g, σ (h₁ * g * h₂) = σ g :=
    fun h₁ h₁m h₂ h₂m g => hσK h₁ (K.inf_le_right K₀ h₁m) h₂ (K.inf_le_right K₀ h₂m) g
  have htrL : ∀ N : ℝ, truncate σ N (F : G → ℂ) ∈ levelSubmodule Ξ σ L.toSubgroup :=
    fun N => ⟨IsBiInvariant.truncate hFL.1 hσL N,
      fun r => lt_of_le_of_lt (nu_truncate_le N r _) (hFL.2 r)⟩
  let uL : ℕ → Level Ξ σ L := fun n =>
    (⟨truncate σ n (F : G → ℂ), htrL n⟩ : levelSubmodule Ξ σ L.toSubgroup)
  have hconv : Tendsto uL atTop (𝓝 fL) := by
    rw [(Level.withSeminorms L).tendsto_nhds]
    intro r ε hε
    set C := (nu Ξ σ (r + 1) (F : G → ℂ)).toReal
    have hlim : Tendsto (fun n : ℕ => C * (1 / ((n : ℝ) + 1))) atTop (𝓝 (C * 0)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul C
    rw [mul_zero] at hlim
    filter_upwards [(tendsto_order.1 hlim).2 ε hε] with n hn
    refine lt_of_le_of_lt ?_ hn
    change (nu Ξ σ r (truncate σ n (F : G → ℂ) - (F : G → ℂ))).toReal ≤ _
    have hneg : truncate σ n (F : G → ℂ) - (F : G → ℂ) =
        -((F : G → ℂ) - truncate σ n (F : G → ℂ)) := (neg_sub _ _).symm
    rw [hneg, nu_neg]
    have hb := nu_sub_truncate_le (σ := σ) hΞ (Nat.cast_nonneg n) r (F : G → ℂ)
    have hfin : ENNReal.ofReal (1 + (n : ℝ))⁻¹ * nu Ξ σ (r + 1) (F : G → ℂ) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hFL.2 (r + 1)).ne
    refine le_trans (ENNReal.toReal_mono hfin hb) (le_of_eq ?_)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr (by positivity))]
    rw [one_div, add_comm (n : ℝ) 1, mul_comm]
  have hmap : Tendsto (fun n : ℕ => Space.ofLevel L (uL n)) atTop (𝓝 (Space.ofLevel L fL)) :=
    ((Space.continuous_ofLevel L).tendsto fL).comp hconv
  have hF : Space.ofLevel L fL = F := Space.ext fun _ => rfl
  rw [hF] at hmap
  refine mem_closure_of_tendsto hmap (Eventually.of_forall fun n => ?_)
  refine ⟨truncateSchwartzBruhat K₀ hσK hσN hFK.1 n, Space.ext fun _ => rfl⟩

end TopologicalGroup

end Langlands.HarishChandraSchwartz
