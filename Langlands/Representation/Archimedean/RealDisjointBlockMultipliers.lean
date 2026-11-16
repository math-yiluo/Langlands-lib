import Langlands.Representation.Archimedean.RealBlockFrobeniusMap

/-!
# Commutation of real block multipliers on disjoint coordinate pairs

Finite Fourier multiplier sums commute on disjoint blocks. The compact formula for
block Frobenius maps then gives an exact commutative square whenever its two paths
use the same respective multipliers and have the same target standard module.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean
namespace RealDisjointBlockMultipliers

open RealBlockFourierFinite RealBlockJacquet RealBlockFrobeniusMap
open Langlands.LocalFactor.Archimedean

variable {n : ℕ}

/-- The normalized Fourier multiplier sum on the finite window `[-D,D]`. -/
def finiteMultiplier (n p D : ℕ) (μ : ℤ → ℂ)
    (f : Langlands.GeneralLinear n ℝ → ℂ) : Langlands.GeneralLinear n ℝ → ℂ :=
  fun g => (2 * (Real.pi : ℂ))⁻¹ *
    ∑ j ∈ Finset.Icc (-(D : ℤ)) D, μ j * blockFourierCoefficient n p j f g

/-- A block Fourier coefficient at a compact point depends only on compact values. -/
theorem coefficient_congr_on_compact (p : ℕ) (j : ℤ)
    {f g : Langlands.GeneralLinear n ℝ → ℂ}
    (hfg : ∀ k ∈ unitaryCompact ℝ n, f k = g k)
    {k : Langlands.GeneralLinear n ℝ} (hk : k ∈ unitaryCompact ℝ n) :
    blockFourierCoefficient n p j f k = blockFourierCoefficient n p j g k := by
  unfold blockFourierCoefficient
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  rw [hfg _ (mul_mem (blockRotation_mem_unitaryCompact n p θ) hk)]

/-- A finite multiplier sum at a compact point depends only on compact values. -/
theorem finiteMultiplier_congr_on_compact (p D : ℕ) (μ : ℤ → ℂ)
    {f g : Langlands.GeneralLinear n ℝ → ℂ}
    (hfg : ∀ k ∈ unitaryCompact ℝ n, f k = g k)
    {k : Langlands.GeneralLinear n ℝ} (hk : k ∈ unitaryCompact ℝ n) :
    finiteMultiplier n p D μ f k = finiteMultiplier n p D μ g k := by
  unfold finiteMultiplier
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [coefficient_congr_on_compact p j hfg hk]

theorem finiteMultiplier_zero (p D : ℕ) (μ : ℤ → ℂ) :
    finiteMultiplier n p D μ 0 = 0 := by
  funext g
  simp [finiteMultiplier, blockFourierCoefficient_zero_fun]

/-- A finite multiplier commutes with a Fourier coefficient on a disjoint block. -/
theorem coefficient_finiteMultiplier {p q : ℕ}
    (hdis : p + 1 < q ∨ q + 1 < p) (D : ℕ) (μ : ℤ → ℂ)
    {f : Langlands.GeneralLinear n ℝ → ℂ} (hf : Continuous f) (j : ℤ)
    (g : Langlands.GeneralLinear n ℝ) :
    blockFourierCoefficient n q j (finiteMultiplier n p D μ f) g =
      finiteMultiplier n p D μ (blockFourierCoefficient n q j f) g := by
  rw [blockFourierCoefficient_eq_coeff]
  change coeff j (fun θ => (2 * (Real.pi : ℂ))⁻¹ *
      ∑ i ∈ Finset.Icc (-(D : ℤ)) D, μ i *
        blockFourierCoefficient n p i f (blockRotation n q θ * g)) = _
  rw [coeff_const_mul, coeff_finset_sum]
  · unfold finiteMultiplier
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [coeff_const_mul]
    change μ i * blockFourierCoefficient n q j (blockFourierCoefficient n p i f) g =
      μ i * blockFourierCoefficient n p i (blockFourierCoefficient n q j f) g
    rw [blockFourierCoefficient_comm (Or.symm hdis) hf]
  · intro i _
    exact continuous_const.mul
      ((continuous_blockFourierCoefficient p i hf).comp
        ((continuous_blockRotation n q).mul continuous_const))

/-- Finite multiplier sums on disjoint blocks commute, without a recurrence premise. -/
theorem finiteMultiplier_comm {p q : ℕ}
    (hdis : p + 1 < q ∨ q + 1 < p) (D E : ℕ) (μ ν : ℤ → ℂ)
    {f : Langlands.GeneralLinear n ℝ → ℂ} (hf : Continuous f) :
    finiteMultiplier n q E ν (finiteMultiplier n p D μ f) =
      finiteMultiplier n p D μ (finiteMultiplier n q E ν f) := by
  funext g
  change (2 * (Real.pi : ℂ))⁻¹ *
      ∑ j ∈ Finset.Icc (-(E : ℤ)) E, ν j *
        blockFourierCoefficient n q j (finiteMultiplier n p D μ f) g =
    (2 * (Real.pi : ℂ))⁻¹ *
      ∑ i ∈ Finset.Icc (-(D : ℤ)) D, μ i *
        blockFourierCoefficient n p i (finiteMultiplier n q E ν f) g
  simp_rw [coefficient_finiteMultiplier hdis D μ hf,
    coefficient_finiteMultiplier (Or.symm hdis) E ν hf]
  simp only [finiteMultiplier]
  simp_rw [← mul_assoc, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [blockFourierCoefficient_comm hdis hf]
  ring

variable {ds es : List RealBlock} {p : ℕ} {ε : ℤ} {σ : ℂ} {μ : ℤ → ℂ}

/-- A uniform source Fourier bound turns a Frobenius map into a finite multiplier on `O(n)`. -/
theorem blockFrobMap_eq_finiteMultiplier
    (h : IsBlockFrobData n ds es p ε σ μ)
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
    (D : ℕ)
    (hD : ∀ j : ℤ, (D : ℤ) < |j| → ∀ g ∈ unitaryCompact ℝ n,
      blockFourierCoefficient n p j f g = 0)
    {g : Langlands.GeneralLinear n ℝ} (hg : g ∈ unitaryCompact ℝ n) :
    ((blockFrobMap h f :
      kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n)) :
        Langlands.GeneralLinear n ℝ → ℂ) g =
      finiteMultiplier n p D μ f g := by
  rw [blockFrobMap_apply_of_mem h f hg, finiteMultiplier]
  congr 1
  apply finsum_eq_sum_of_support_subset
  intro j hj
  by_contra hjI
  change j ∉ Finset.Icc (-(D : ℤ)) D at hjI
  have hjD : (D : ℤ) < |j| := by
    rw [Finset.mem_Icc, ← abs_le] at hjI
    exact not_le.mp hjI
  apply hj
  dsimp only
  rw [hD j hjD g hg, mul_zero]

/-- A Frobenius map preserves a uniform Fourier bound along a disjoint block. -/
theorem blockFrobMap_preserves_disjoint_bound {q : ℕ}
    (hdis : p + 1 < q ∨ q + 1 < p)
    (h : IsBlockFrobData n ds es p ε σ μ)
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
    (E : ℕ)
    (hE : ∀ j : ℤ, (E : ℤ) < |j| → ∀ g ∈ unitaryCompact ℝ n,
      blockFourierCoefficient n q j f g = 0) :
    ∀ j : ℤ, (E : ℤ) < |j| → ∀ g ∈ unitaryCompact ℝ n,
      blockFourierCoefficient n q j
        ((blockFrobMap h f :
          kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n)) :
            Langlands.GeneralLinear n ℝ → ℂ) g = 0 := by
  obtain ⟨D, hD⟩ := exists_bound_coe p f
  intro j hj g hg
  rw [coefficient_congr_on_compact q j
    (fun k hk => blockFrobMap_eq_finiteMultiplier h f D hD hk) hg,
    coefficient_finiteMultiplier hdis D μ (continuous_coe f)]
  have hz : ∀ k ∈ unitaryCompact ℝ n,
      blockFourierCoefficient n q j (f : Langlands.GeneralLinear n ℝ → ℂ) k =
        (0 : Langlands.GeneralLinear n ℝ → ℂ) k := fun k hk => hE j hj k hk
  rw [finiteMultiplier_congr_on_compact p D μ hz hg, finiteMultiplier_zero]
  rfl

/-- A square of block Frobenius maps commutes if its two coordinate pairs are disjoint
and the multiplier on each pair is the same on both paths. -/
theorem blockFrobMap_commuting_square
    {xs ys zs ws : List RealBlock} {q : ℕ} {ε' : ℤ} {σ' : ℂ} {ν : ℤ → ℂ}
    (hdis : p + 1 < q ∨ q + 1 < p)
    (hp : IsBlockFrobData n xs ys p ε σ μ)
    (hq : IsBlockFrobData n xs zs q ε' σ' ν)
    (hq' : IsBlockFrobData n ys ws q ε' σ' ν)
    (hp' : IsBlockFrobData n zs ws p ε σ μ)
    (f : kFiniteFunctions (realStandardModule n xs) (unitaryCompact ℝ n)) :
    blockFrobMap hq' (blockFrobMap hp f) = blockFrobMap hp' (blockFrobMap hq f) := by
  obtain ⟨D, hD⟩ := exists_bound_coe p f
  obtain ⟨E, hE⟩ := exists_bound_coe q f
  have hD' := blockFrobMap_preserves_disjoint_bound (Or.symm hdis) hq f D hD
  have hE' := blockFrobMap_preserves_disjoint_bound hdis hp f E hE
  apply Subtype.ext
  apply eq_of_eqOn_unitaryCompact_of_mem_principalSeries
    (blockFrobMap hq' (blockFrobMap hp f)).2.1.1
    (blockFrobMap hp' (blockFrobMap hq f)).2.1.1
  intro k hk
  rw [blockFrobMap_eq_finiteMultiplier hq' _ E hE' hk,
    finiteMultiplier_congr_on_compact q E ν
      (fun g hg => blockFrobMap_eq_finiteMultiplier hp f D hD hg) hk,
    blockFrobMap_eq_finiteMultiplier hp' _ D hD' hk,
    finiteMultiplier_congr_on_compact p D μ
      (fun g hg => blockFrobMap_eq_finiteMultiplier hq f E hE hg) hk,
    finiteMultiplier_comm hdis D E μ ν (continuous_coe f)]

end RealDisjointBlockMultipliers
end Langlands.Archimedean
