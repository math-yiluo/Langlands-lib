import Langlands.Representation.Archimedean.RealInducedPairFrobenius
import Langlands.Representation.Archimedean.RealAdjacentMultiplierInjectivity

/-!
# Kernels of the four-crossing induced-pair operator

The original induction windows control the first crossing. The windows recovered
after two crossings control the next crossing in either middle order.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

namespace RealInducedPairKernelRecovery

open RealBlockFrobeniusMap RealBlockMultiplier RealBlockJacquet
open RealInducedPairFrobenius RealAdjacentMultiplier

/-- A Frobenius kernel is detected by the source coefficients on the support of
its multiplier. The coefficient identity is needed only on the compact group. -/
theorem blockFrobMap_eq_zero_iff {n : ℕ} {ds es : List RealBlock} {p : ℕ}
    {ε : ℤ} {σ : ℂ} {μ : ℤ → ℂ} (h : IsBlockFrobData n ds es p ε σ μ)
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) :
    blockFrobMap h f = 0 ↔
      ∀ k ∈ unitaryCompact ℝ n, ∀ j : ℤ, μ j ≠ 0 →
        blockFourierCoefficient n p j f k = 0 := by
  constructor
  · intro hf k hk j hj
    have heq := blockFourierCoefficient_blockFrobMap h f hk j
    rw [hf, ZeroMemClass.coe_zero, blockFourierCoefficient_zero_fun] at heq
    exact (mul_eq_zero.mp heq.symm).resolve_left hj
  · intro hf
    refine eq_of_blockFourierCoefficient_eq h.lt fun j k hk => ?_
    rw [ZeroMemClass.coe_zero, blockFourierCoefficient_zero_fun,
      blockFourierCoefficient_blockFrobMap h f hk j]
    by_cases hj : μ j = 0
    · rw [hj, zero_mul]
    · rw [hf k hk j hj, mul_zero]

/-- Opposite parity excludes the boundary of a tail multiplier. -/
theorem abs_ne_cutoff {ℓ : ℕ} {ε j : ℤ}
    (hℓ : Even ((ℓ : ℤ) - 1 - ε)) (hj : Even (j - ε)) :
    |j| ≠ (ℓ : ℤ) := by
  rw [Int.even_iff] at hℓ hj
  rcases le_or_gt 0 j with hj0 | hj0
  · rw [abs_of_nonneg hj0]
    omega
  · rw [abs_of_neg hj0]
    omega

/-- For a tail multiplier, the kernel consists exactly of vectors with no modes
at or above the cutoff. The boundary mode vanishes by parity. -/
theorem blockFrobMap_eq_zero_iff_tail {n : ℕ} {ds es : List RealBlock} {p : ℕ}
    {ε : ℤ} {σ : ℂ} {μ : ℤ → ℂ} (h : IsBlockFrobData n ds es p ε σ μ)
    (ℓ : ℕ) (hℓ : Even ((ℓ : ℤ) - 1 - ε))
    (hμ : ∀ j : ℤ, Even (j - ε) → (μ j ≠ 0 ↔ (ℓ : ℤ) < |j|))
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) :
    blockFrobMap h f = 0 ↔
      ∀ k ∈ unitaryCompact ℝ n, ∀ j : ℤ, (ℓ : ℤ) ≤ |j| →
        blockFourierCoefficient n p j f k = 0 := by
  constructor
  · intro hf k hk j hj
    by_cases hje : Even (j - ε)
    · exact (blockFrobMap_eq_zero_iff h f).mp hf k hk j
        ((hμ j hje).mpr (lt_of_le_of_ne hj (Ne.symm (abs_ne_cutoff hℓ hje))))
    · exact blockFourierCoefficient_eq_zero_of_not_even h.lt h.par f hje k
  · intro hf
    refine eq_of_blockFourierCoefficient_eq h.lt fun j k hk => ?_
    rw [ZeroMemClass.coe_zero, blockFourierCoefficient_zero_fun,
      blockFourierCoefficient_blockFrobMap h f hk j]
    by_cases hje : Even (j - ε)
    · by_cases hj : μ j = 0
      · rw [hj, zero_mul]
      · rw [hf k hk j ((hμ j hje).mp hj).le, mul_zero]
    · rw [blockFourierCoefficient_eq_zero_of_not_even h.lt h.par f hje k, mul_zero]

variable {d e : ComplexCharacterData} {δ : ℂ} {μ₁ μ₀ μ₂ μ₃ : ℤ → ℂ}
    (h : MultiplierData d e δ μ₁ μ₀ μ₂ μ₃)

include h

/-- Restrict the first full-character multiplier to the actual source module. -/
def firstMultiplier : CompactMultiplier 4 (src d e) 1 μ₁ where
  toLinearMap := (KF (l1 d e)).subtype.comp h.to1
  fourier _f _k hk j := blockFourierCoefficient_blockFrobMap h.data1 _ hk j

/-- Either original induction window makes the first crossing injective if
the possible zeros lie below its absolute weight. -/
theorem to1_injective_of_cutoff (m : ℕ)
    (hm : m < d.weight.natAbs ∨ m < e.weight.natAbs)
    (hμ : ∀ j : ℤ, Even (j - ((e.weight.natAbs + 1 : ℕ) : ℤ)) →
      (m : ℤ) ≤ |j| → μ₁ j ≠ 0) :
    Function.Injective h.to1 := by
  have hpar := h.data1.par
  rw [posChar_l0] at hpar
  have hi : Function.Injective (firstMultiplier h).toLinearMap := by
    rcases hm with hm | hm
    · exact injective_of_induced (n := 4) 0 (by decide) (Or.inl ⟨rfl, rfl⟩)
        (firstMultiplier h) (d := d) rfl hm hpar hμ
    · exact injective_of_induced (n := 4) 1 (by decide) (Or.inr ⟨rfl, rfl⟩)
        (firstMultiplier h) (d := e) rfl hm hpar hμ
  intro f g hfg
  exact hi (congrArg (fun z : KF (l1 d e) =>
    (z : Langlands.GeneralLinear 4 ℝ → ℂ)) hfg)

/-- The exact spectral description of the first singular kernel retains both
source induction constraints. -/
theorem to1_eq_zero_iff_tail (ℓ : ℕ)
    (hℓ : Even ((ℓ : ℤ) - 1 - ((e.weight.natAbs + 1 : ℕ) : ℤ)))
    (hμ : ∀ j : ℤ, Even (j - ((e.weight.natAbs + 1 : ℕ) : ℤ)) →
      (μ₁ j ≠ 0 ↔ (ℓ : ℤ) < |j|)) (f : KF (src d e)) :
    h.to1 f = 0 ↔
      ∀ k ∈ unitaryCompact ℝ 4, ∀ j : ℤ, (ℓ : ℤ) ≤ |j| →
        blockFourierCoefficient 4 1 j f k = 0 :=
  blockFrobMap_eq_zero_iff_tail h.data1 ℓ hℓ hμ
    (Submodule.inclusion (src_le_l0 d e) f)

/-- In particular, a tail crossing below either source weight has trivial
kernel even though the multiplier has zeros. -/
theorem to1_injective_of_tail (ℓ : ℕ)
    (hℓ : Even ((ℓ : ℤ) - 1 - ((e.weight.natAbs + 1 : ℕ) : ℤ)))
    (hμ : ∀ j : ℤ, Even (j - ((e.weight.natAbs + 1 : ℕ) : ℤ)) →
      (μ₁ j ≠ 0 ↔ (ℓ : ℤ) < |j|))
    (hlt : ℓ < d.weight.natAbs ∨ ℓ < e.weight.natAbs) :
    Function.Injective h.to1 := by
  apply to1_injective_of_cutoff h ℓ hlt
  intro j hj hbound
  exact (hμ j hj).mpr (lt_of_le_of_ne hbound (Ne.symm (abs_ne_cutoff hℓ hj)))

omit h in
theorem tD_le_l10 : KF (tD d e) ≤ KF (l10 d e) := by
  refine kf_le (posChar_tD d e).symm ?_
  intro p x hx
  rcases p with _ | _ | _ | _ | p <;> simp [realInducedBlockAt] at hx

omit h in
theorem tE_le_l12 : KF (tE d e) ≤ KF (l12 d e) := by
  refine kf_le (posChar_tE d e).symm ?_
  intro p x hx
  rcases p with _ | _ | _ | _ | p <;> simp [realInducedBlockAt] at hx

/-- The right middle crossing, on the module with its recovered d-window. -/
def rightMultiplier : CompactMultiplier 4 (tD d e) 2 μ₂ where
  toLinearMap := (KF (l3 d e)).subtype.comp
    ((blockFrobMap h.data20).comp (Submodule.inclusion (tD_le_l10 (d := d) (e := e))))
  fourier _f _k hk j := blockFourierCoefficient_blockFrobMap h.data20 _ hk j

/-- The left middle crossing, on the module with its recovered e-window. -/
def leftMultiplier : CompactMultiplier 4 (tE d e) 0 μ₀ where
  toLinearMap := (KF (l3 d e)).subtype.comp
    ((blockFrobMap h.data02).comp (Submodule.inclusion (tE_le_l12 (d := d) (e := e))))
  fourier _f _k hk j := blockFourierCoefficient_blockFrobMap h.data02 _ hk j

/-- A right middle cutoff below the recovered d-weight does not enlarge the
kernel accumulated in the first two crossings. -/
theorem to3_eq_zero_iff_to10 (m : ℕ) (hm : m < d.weight.natAbs)
    (hμ : ∀ j : ℤ, Even (j - 0) → (m : ℤ) ≤ |j| → μ₂ j ≠ 0)
    (f : KF (src d e)) :
    h.to3 f = 0 ↔ h.to10 f = 0 := by
  have hpar := h.data20.par
  rw [← posChar_tD] at hpar
  have hi := injective_of_induced (n := 4) 1 (by decide) (Or.inl ⟨rfl, rfl⟩)
    (rightMultiplier h) (d := d) rfl hm hpar hμ
  constructor
  · intro hf
    have heq : (rightMultiplier h).toLinearMap ⟨_, h.landing10 f⟩ =
        (rightMultiplier h).toLinearMap 0 := by
      rw [map_zero]
      exact congrArg (fun z : KF (l3 d e) =>
        (z : Langlands.GeneralLinear 4 ℝ → ℂ)) hf
    exact Subtype.ext (congrArg (fun z : KF (tD d e) =>
      (z : Langlands.GeneralLinear 4 ℝ → ℂ)) (hi heq))
  · intro hf
    change blockFrobMap h.data20 (h.to10 f) = 0
    rw [hf, map_zero]

/-- The other middle order gives the same kernel recovery using the e-window. -/
theorem to3_eq_zero_iff_to12 (m : ℕ) (hm : m < e.weight.natAbs)
    (hμ : ∀ j : ℤ, Even (j - ((d.weight.natAbs + e.weight.natAbs + 2 : ℕ) : ℤ)) →
      (m : ℤ) ≤ |j| → μ₀ j ≠ 0) (f : KF (src d e)) :
    h.to3 f = 0 ↔ h.to12 f = 0 := by
  have hpar := h.data02.par
  rw [← posChar_tE] at hpar
  have hi := injective_of_induced (n := 4) 0 (by decide) (Or.inr ⟨rfl, rfl⟩)
    (leftMultiplier h) (d := e) rfl hm hpar hμ
  constructor
  · intro hf
    have heq : (leftMultiplier h).toLinearMap ⟨_, h.landing12 f⟩ =
        (leftMultiplier h).toLinearMap 0 := by
      rw [map_zero]
      rw [h.to3_eq f] at hf
      exact congrArg (fun z : KF (l3 d e) =>
        (z : Langlands.GeneralLinear 4 ℝ → ℂ)) hf
    exact Subtype.ext (congrArg (fun z : KF (tE d e) =>
      (z : Langlands.GeneralLinear 4 ℝ → ℂ)) (hi heq))
  · intro hf
    rw [h.to3_eq f, hf, map_zero]

theorem ker_to3_eq_ker_to10 (m : ℕ) (hm : m < d.weight.natAbs)
    (hμ : ∀ j : ℤ, Even (j - 0) → (m : ℤ) ≤ |j| → μ₂ j ≠ 0) :
    LinearMap.ker h.to3 = LinearMap.ker h.to10 := by
  ext f
  exact to3_eq_zero_iff_to10 h m hm hμ f

theorem ker_to3_eq_ker_to12 (m : ℕ) (hm : m < e.weight.natAbs)
    (hμ : ∀ j : ℤ, Even (j - ((d.weight.natAbs + e.weight.natAbs + 2 : ℕ) : ℤ)) →
      (m : ℤ) ≤ |j| → μ₀ j ≠ 0) :
    LinearMap.ker h.to3 = LinearMap.ker h.to12 := by
  ext f
  exact to3_eq_zero_iff_to12 h m hm hμ f

end RealInducedPairKernelRecovery

/-- The recovered induction windows control the two possible middle kernels. -/
def RealInducedPairKernelRecoveryStatement : Prop :=
  ∀ (d e : ComplexCharacterData) (δ : ℂ) (μ₁ μ₀ μ₂ μ₃ : ℤ → ℂ)
    (h : RealInducedPairFrobenius.MultiplierData d e δ μ₁ μ₀ μ₂ μ₃),
    (∀ m : ℕ, m < d.weight.natAbs →
      (∀ j : ℤ, Even (j - 0) → (m : ℤ) ≤ |j| → μ₂ j ≠ 0) →
      LinearMap.ker h.to3 = LinearMap.ker h.to10) ∧
    (∀ m : ℕ, m < e.weight.natAbs →
      (∀ j : ℤ, Even (j - ((d.weight.natAbs + e.weight.natAbs + 2 : ℕ) : ℤ)) →
        (m : ℤ) ≤ |j| → μ₀ j ≠ 0) →
      LinearMap.ker h.to3 = LinearMap.ker h.to12)

theorem realInducedPairKernelRecovery : RealInducedPairKernelRecoveryStatement := by
  intro d e δ μ₁ μ₀ μ₂ μ₃ h
  exact ⟨RealInducedPairKernelRecovery.ker_to3_eq_ker_to10 h,
    RealInducedPairKernelRecovery.ker_to3_eq_ker_to12 h⟩

end Langlands.Archimedean
