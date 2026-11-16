import Langlands.Representation.Archimedean.RealInductionStagesSlice
import Langlands.Representation.Archimedean.RealDisjointBlockMultipliers

/-!
# Block Fourier multipliers under normalized induction slices

Finite multiplier compositions commute exactly with normalized slices. A supplied
local two-step landing theorem also transfers to any consecutive ambient block.
-/

noncomputable section

open scoped Matrix Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean
namespace RealBlockMultiplierSlices

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open InductionStages RealDisjointBlockMultipliers

/-- Apply the finite multiplier on `p`, followed by the finite multiplier on `q`. -/
def twoStep (n p q D E : ℕ) (μ ν : ℤ → ℂ)
    (f : Langlands.GeneralLinear n ℝ → ℂ) : Langlands.GeneralLinear n ℝ → ℂ :=
  finiteMultiplier n q E ν (finiteMultiplier n p D μ f)

variable {n a r : ℕ}

/-- A finite multiplier commutes with the normalized slice on any included rotation. -/
theorem finiteMultiplier_slice (h : a + r ≤ n) {p : ℕ} (hp : p + 1 < r)
    (D : ℕ) (μ : ℤ → ℂ) (κ : Langlands.GeneralLinear n ℝ)
    (f : Langlands.GeneralLinear n ℝ → ℂ) :
    finiteMultiplier r p D μ (slice h κ f) =
      slice h κ (finiteMultiplier n (a + p) D μ f) := by
  funext g
  simp only [finiteMultiplier, blockFourierCoefficient_slice h hp, slice_apply]
  simp_rw [← mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Two consecutive finite multipliers commute with the normalized slice. -/
theorem twoStep_slice (h : a + r ≤ n) {p q : ℕ}
    (hp : p + 1 < r) (hq : q + 1 < r) (D E : ℕ) (μ ν : ℤ → ℂ)
    (κ : Langlands.GeneralLinear n ℝ) (f : Langlands.GeneralLinear n ℝ → ℂ) :
    twoStep r p q D E μ ν (slice h κ f) =
      slice h κ (twoStep n (a + p) (a + q) D E μ ν f) := by
  unfold twoStep
  rw [finiteMultiplier_slice h hp, finiteMultiplier_slice h hq]

/-- Compact Fourier multiplier relations pass to every compact slice. -/
theorem multiplier_relation_slice (h : a + r ≤ n) {p : ℕ} (hp : p + 1 < r)
    (μ : ℤ → ℂ) {κ : Langlands.GeneralLinear n ℝ}
    (hκ : κ ∈ unitaryCompact ℝ n)
    {f H : Langlands.GeneralLinear n ℝ → ℂ}
    (hμ : ∀ g ∈ unitaryCompact ℝ n, ∀ j : ℤ,
      blockFourierCoefficient n (a + p) j H g =
        μ j * blockFourierCoefficient n (a + p) j f g) :
    ∀ g ∈ unitaryCompact ℝ r, ∀ j : ℤ,
      blockFourierCoefficient r p j (slice h κ H) g =
        μ j * blockFourierCoefficient r p j (slice h κ f) g := by
  intro g hg j
  rw [blockFourierCoefficient_slice h hp, blockFourierCoefficient_slice h hp,
    hμ _ (mul_mem (blockEmb_mem_unitaryCompact h hg) hκ)]
  ring

/-- Transfer a supplied local two-step landing theorem through arbitrary surrounding
blocks. Smooth ambient intermediate functions supply continuous local slices. -/
theorem twoStep_landing_in_stages {pre ds post : List RealBlock}
    (h : a + r ≤ n) (ha : realRank pre = a) (hr : realRank ds = r)
    {p q t L : ℕ} (hp : p + 1 < r) (hq : q + 1 < r) (ht : t + 1 < r)
    (μ ν : ℤ → ℂ)
    (hlocal : ∀ (f H U : Langlands.GeneralLinear r ℝ → ℂ),
      f ∈ KFin r ds → Continuous H → Continuous U →
      (∀ g ∈ unitaryCompact ℝ r, ∀ j : ℤ,
        blockFourierCoefficient r p j H g =
          μ j * blockFourierCoefficient r p j f g) →
      (∀ g ∈ unitaryCompact ℝ r, ∀ j : ℤ,
        blockFourierCoefficient r q j U g =
          ν j * blockFourierCoefficient r q j H g) →
      ∀ g ∈ unitaryCompact ℝ r, ∀ j : ℤ, |j| < (L : ℤ) →
        blockFourierCoefficient r t j U g = 0)
    (f : KFin n (pre ++ ds ++ post))
    {H U : Langlands.GeneralLinear n ℝ → ℂ}
    (hH : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ H)
    (hU : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ U)
    (hμ : ∀ g ∈ unitaryCompact ℝ n, ∀ j : ℤ,
      blockFourierCoefficient n (a + p) j H g =
        μ j * blockFourierCoefficient n (a + p) j f g)
    (hν : ∀ g ∈ unitaryCompact ℝ n, ∀ j : ℤ,
      blockFourierCoefficient n (a + q) j U g =
        ν j * blockFourierCoefficient n (a + q) j H g) :
    ∀ g ∈ unitaryCompact ℝ n, ∀ j : ℤ, |j| < (L : ℤ) →
      blockFourierCoefficient n (a + t) j U g = 0 := by
  intro κ hκ j hj
  have hres := hlocal (slice h κ (f : Langlands.GeneralLinear n ℝ → ℂ))
    (slice h κ H) (slice h κ U)
    (slice_mem_kFin h ha hr hκ f.2)
    (contMDiff_slice h κ hH).continuous (contMDiff_slice h κ hU).continuous
    (multiplier_relation_slice h hp μ hκ hμ)
    (multiplier_relation_slice h hq ν hκ hν)
    1 (one_mem _) j hj
  simpa only [blockFourierCoefficient_slice h ht, sliceFactor_one,
    map_one, one_mul] using hres

end RealBlockMultiplierSlices
end Langlands.Archimedean
