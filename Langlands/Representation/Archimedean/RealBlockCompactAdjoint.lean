import Langlands.Representation.Archimedean.PrincipalSeriesAnnihilator
import Langlands.Representation.Archimedean.RealSwapFLanding

/-! # Self-adjoint real block multipliers in the compact principal-series model -/

noncomputable section

open MeasureTheory
open scoped ComplexConjugate InnerProductSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean
namespace RealBlockCompactAdjoint

open PrincipalSeriesAnnihilator RealPrincipalSeriesDuality
open RealBlockFourierFinite RealBlockTransposition RealSwapFLanding

attribute [local instance] measurableSpaceK
local instance borelSpaceK' (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

variable {n p : ℕ} {χ : ℕ → ℝˣ → ℂ}

/-- Pointwise complex conjugation on functions, as a semilinear map. -/
def conjugate : (Langlands.GeneralLinear n ℝ → ℂ) →ₛₗ[starRingEnd ℂ]
    (Langlands.GeneralLinear n ℝ → ℂ) where
  toFun f g := conj (f g)
  map_add' f g := by funext x; simp
  map_smul' c f := by funext x; simp

/-- Pointwise conjugation preserves right compact finiteness. -/
theorem conjugate_mem_kFiniteVectors {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ))
      (unitaryCompact ℝ n)) :
    conjugate f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ))
      (unitaryCompact ℝ n) := by
  rw [mem_kFiniteVectors_iff] at hf ⊢
  have e : (Set.range fun k : unitaryCompact ℝ n =>
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
        (k : Langlands.GeneralLinear n ℝ) (conjugate f)) =
      conjugate '' Set.range fun k : unitaryCompact ℝ n =>
        Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
          (k : Langlands.GeneralLinear n ℝ) f := by
    rw [← Set.range_comp]
    rfl
  rw [e, ← Submodule.map_span]
  exact (Submodule.fg_iff_finiteDimensional _).mp
    (((Submodule.fg_iff_finiteDimensional _).mpr hf).map conjugate)

/-- A Fourier multiplier and its complex conjugate are adjoint in the compact model. -/
theorem inner_eq_of_multiplier (hp : p + 1 < n)
    (x x' y y' : KFin n χ) (μ : ℤ → ℂ)
    (hx : ∀ j : ℤ, ∀ k ∈ unitaryCompact ℝ n,
      blockFourierCoefficient n p j x'.toFun k = μ j * blockFourierCoefficient n p j x.toFun k)
    (hy : ∀ j : ℤ, ∀ k ∈ unitaryCompact ℝ n,
      blockFourierCoefficient n p j y'.toFun k = conj (μ j) *
        blockFourierCoefficient n p j y.toFun k) :
    ⟪x', y⟫_ℂ = ⟪x, y'⟫_ℂ := by
  rw [inner_eq, inner_eq]
  apply integral_mul_eq_of_multiplier hp
    (Complex.continuous_conj.comp x.continuous_toFun)
    (Complex.continuous_conj.comp x'.continuous_toFun)
    y.continuous_toFun y'.continuous_toFun
    (conjugate_mem_kFiniteVectors x.toFun_mem.2)
    (conjugate_mem_kFiniteVectors x'.toFun_mem.2)
    y.toFun_mem.2 y'.toFun_mem.2 (fun j => conj (μ (-j)))
  · intro j k hk
    change blockFourierCoefficient n p j (fun g => conj (x'.toFun g)) k =
      conj (μ (-j)) * blockFourierCoefficient n p j (fun g => conj (x.toFun g)) k
    rw [blockFourierCoefficient_conj, blockFourierCoefficient_conj, hx (-j) k hk, map_mul]
  · intro j k hk
    simpa only [neg_neg] using hy j k hk

/-- Real Fourier multipliers are self-adjoint. -/
theorem inner_eq_of_real_multiplier (hp : p + 1 < n)
    (T : KFin n χ →ₗ[ℂ] KFin n χ) (μ : ℤ → ℂ)
    (hμ : ∀ j, conj (μ j) = μ j)
    (hT : ∀ x j, ∀ k ∈ unitaryCompact ℝ n,
      blockFourierCoefficient n p j (T x).toFun k =
        μ j * blockFourierCoefficient n p j x.toFun k)
    (x y : KFin n χ) : ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ :=
  inner_eq_of_multiplier hp x (T x) y (T y) μ (hT x)
    (fun j k hk => by rw [hμ]; exact hT y j k hk)

/-- Fourier coefficients on the compact group determine a compact-finite principal-series vector. -/
theorem eq_of_fourier (hp : p + 1 < n) {x y : KFin n χ}
    (h : ∀ j k, k ∈ unitaryCompact ℝ n →
      blockFourierCoefficient n p j x.toFun k = blockFourierCoefficient n p j y.toFun k) :
    x = y := by
  apply KFin.ext
  refine eq_of_eqOn_unitaryCompact_of_mem_principalSeries x.toFun_mem.1 y.toFun_mem.1
    fun k hk => ?_
  rw [eq_finsum_blockFourierCoefficient hp x.continuous_toFun x.toFun_mem.2 hk,
    eq_finsum_blockFourierCoefficient hp y.continuous_toFun y.toFun_mem.2 hk]
  congr 2
  funext j
  exact h j k hk

end RealBlockCompactAdjoint

/-- The compact inner product makes a block Fourier multiplier adjoint to the multiplier
whose values are its complex conjugates. -/
def RealBlockCompactAdjointStatement : Prop :=
  ∀ (n p : ℕ) (χ : ℕ → ℝˣ → ℂ) (x x' y y' : PrincipalSeriesAnnihilator.KFin n χ)
    (μ : ℤ → ℂ), p + 1 < n →
    (∀ j k, k ∈ unitaryCompact ℝ n →
      blockFourierCoefficient n p j x'.toFun k = μ j * blockFourierCoefficient n p j x.toFun k) →
    (∀ j k, k ∈ unitaryCompact ℝ n →
      blockFourierCoefficient n p j y'.toFun k = conj (μ j) *
        blockFourierCoefficient n p j y.toFun k) →
    ⟪x', y⟫_ℂ = ⟪x, y'⟫_ℂ

theorem realBlockCompactAdjoint : RealBlockCompactAdjointStatement :=
  fun _ _ _ x x' y y' μ hp hx hy =>
    RealBlockCompactAdjoint.inner_eq_of_multiplier hp x x' y y' μ hx hy

end Langlands.Archimedean
