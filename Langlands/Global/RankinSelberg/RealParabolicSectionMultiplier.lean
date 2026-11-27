import Langlands.Global.RankinSelberg.RealParabolicLeviSlices
import Langlands.Global.RankinSelberg.RealParabolicSmoothSectionMap
import Langlands.Global.RankinSelberg.RealSmoothBlockFourierMultiplier

/-! # Block Fourier operators on compact parabolic sections -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open TopologicalSpace
open scoped Distributions Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealParabolicCompactSection

open RealStandardCompactBanach InductionStages

private local instance (d : ℕ) (ds : List RealBlock) : NormedAddCommGroup (Carrier d ds) :=
  (closureSubmodule (n := d) ds).normedAddCommGroup

private local instance (d : ℕ) (ds : List RealBlock) : NormedSpace ℂ (Carrier d ds) :=
  (closureSubmodule (n := d) ds).normedSpace

local notation "G" => fun d : ℕ => Langlands.GeneralLinear d ℝ
local notation "S" => realStandardModule
local notation:max "D" d:max ds:max => DerivativeSmoothVectors (matrixModel ℝ d) (representation (n := d) ds)
local notation:max "F" ds:max v:max => Subtype.val (LinearEquiv.symm (derivativeEquiv ds) v)

private theorem coefficient_of_slice_eq {N a k p : ℕ} (h : a + k ≤ N) (hp : p + 1 < k)
    (j : ℤ) (u : G N) (H : G N → ℂ) (f : G k → ℂ) (A : G k) (c : ℂ)
    (hs : slice h u H = c • Whittaker.rightTranslation ℂ (G k) A f) :
    blockFourierCoefficient N (a + p) j H u = c * blockFourierCoefficient k p j f A := by
  have he := blockFourierCoefficient_slice h hp j u H 1
  simp only [sliceFactor_one, map_one, one_mul] at he
  rw [← he, hs]
  change blockFourierCoefficient k p j (fun x => c * Whittaker.rightTranslation ℂ (G k) A f x) 1 = _
  rw [RealSwapLandingAlgebra.blockFourierCoefficient_const_mul,
    blockFourierCoefficient_rightTranslation, one_mul]

variable {m n p : ℕ} {d₁ d₂ e : List RealBlock}

local notation "r₁" => m + 1
local notation "N" => (n + m) + 1
local notation "Test" => 𝓓((⊤ : Opens (Matrix (Fin (m + 1)) (Fin n) ℝ)), ℂ)

private theorem reconstruct_section (hm : realRank d₁ = r₁) (hn : realRank d₂ = n)
    (f : S r₁ d₁) (g : S n d₂) (φ : Test) :
    F (d₂ ++ d₁) (smoothSectionVector hm hn f g φ) = standardSection f.val g.val φ := by
  funext u
  simpa only [map_one, Module.End.one_apply, mul_one] using
    reconstruct_translate_smoothSectionVector hm hn f g φ 1 u

set_option maxHeartbeats 610000 in
/-- A matched ambient multiplier acts on the first input by the local multiplier. -/
theorem smoothSectionVector_multiplier_first (hm : realRank d₁ = r₁) (hn : realRank d₂ = n)
    (he : realRank e = r₁) (hp : p + 1 < r₁) (μ : ℤ → ℂ)
    (T : D N (d₂ ++ d₁) →L[ℂ] D N (d₂ ++ e)) (Q : D r₁ d₁ →L[ℂ] D r₁ e)
    (hT : IsSmoothBlockFourierMultiplier (n + p) μ T) (hQ : IsSmoothBlockFourierMultiplier p μ Q)
    (f : S r₁ d₁) (g : S n d₂) (φ : Test) :
    T (smoothSectionVector hm hn f g φ) =
      smoothSectionVector he hn ((derivativeEquiv e).symm (Q (derivativeEquiv d₁ f))) g φ := by
  let v := smoothSectionVector hm hn f g φ
  let f' := (derivativeEquiv e).symm (Q (derivativeEquiv d₁ f))
  let w := smoothSectionVector he hn f' g φ
  change T v = w
  apply (derivativeEquiv (d₂ ++ e)).symm.injective
  apply Subtype.ext
  funext u
  have hN : n + p + 1 < N := by omega
  apply RealSwapLandingAlgebra.eq_of_blockFourierCoefficient_eq hN
    ((derivativeEquiv (d₂ ++ e)).symm (T v)).2.1.1.continuous
    ((derivativeEquiv (d₂ ++ e)).symm w).2.1.1.continuous u
  intro j
  obtain ⟨A, B, c, h⟩ := realParabolicLeviSlices r₁ n φ φ.contDiff φ.hasCompactSupport u
  have hf := coefficient_of_slice_eq (show n + r₁ ≤ N by omega) hp j u _ f.val A _
    (h f.val g.val f.2.1.1 g.2.1.1).1
  have hf' := coefficient_of_slice_eq (show n + r₁ ≤ N by omega) hp j u _ f'.val A _
    (h f'.val g.val f'.2.1.1 g.2.1.1).1
  have hlocal : blockFourierCoefficient r₁ p j f'.val A = μ j * blockFourierCoefficient r₁ p j f.val A := by
    simpa only [LinearEquiv.symm_apply_apply] using hQ j A (derivativeEquiv d₁ f)
  rw [hT j u v, show F (d₂ ++ d₁) v = _ from reconstruct_section hm hn f g φ,
    show F (d₂ ++ e) w = _ from reconstruct_section he hn f' g φ, hf, hf', hlocal]
  ring

set_option maxHeartbeats 610000 in
/-- A matched ambient multiplier acts on the second input by the local multiplier. -/
theorem smoothSectionVector_multiplier_second (hm : realRank d₁ = r₁) (hn : realRank d₂ = n)
    (he : realRank e = n) (hp : p + 1 < n) (μ : ℤ → ℂ)
    (T : D N (d₂ ++ d₁) →L[ℂ] D N (e ++ d₁)) (Q : D n d₂ →L[ℂ] D n e)
    (hT : IsSmoothBlockFourierMultiplier p μ T) (hQ : IsSmoothBlockFourierMultiplier p μ Q)
    (f : S r₁ d₁) (g : S n d₂) (φ : Test) :
    T (smoothSectionVector hm hn f g φ) =
      smoothSectionVector hm he f ((derivativeEquiv e).symm (Q (derivativeEquiv d₂ g))) φ := by
  let v := smoothSectionVector hm hn f g φ
  let g' := (derivativeEquiv e).symm (Q (derivativeEquiv d₂ g))
  let w := smoothSectionVector hm he f g' φ
  change T v = w
  apply (derivativeEquiv (e ++ d₁)).symm.injective
  apply Subtype.ext
  funext u
  have hN : p + 1 < N := by omega
  apply RealSwapLandingAlgebra.eq_of_blockFourierCoefficient_eq hN
    ((derivativeEquiv (e ++ d₁)).symm (T v)).2.1.1.continuous
    ((derivativeEquiv (e ++ d₁)).symm w).2.1.1.continuous u
  intro j
  obtain ⟨A, B, c, h⟩ := realParabolicLeviSlices r₁ n φ φ.contDiff φ.hasCompactSupport u
  have hg := coefficient_of_slice_eq (show 0 + n ≤ N by omega) hp j u _ g.val B _
    (h f.val g.val f.2.1.1 g.2.1.1).2
  have hg' := coefficient_of_slice_eq (show 0 + n ≤ N by omega) hp j u _ g'.val B _
    (h f.val g'.val f.2.1.1 g'.2.1.1).2
  have hlocal : blockFourierCoefficient n p j g'.val B = μ j * blockFourierCoefficient n p j g.val B := by
    simpa only [LinearEquiv.symm_apply_apply] using hQ j B (derivativeEquiv d₂ g)
  simp only [zero_add] at hg hg'
  rw [hT j u v, show F (d₂ ++ d₁) v = _ from reconstruct_section hm hn f g φ,
    show F (e ++ d₁) w = _ from reconstruct_section hm he f g' φ, hg, hg', hlocal]
  ring

/-- Applying a matched ambient block multiplier to a pure compact section agrees with
applying the local multiplier to the corresponding Levi input. -/
def RealParabolicSectionMultiplierStatement : Prop :=
  ∀ (m n p : ℕ) (d₁ d₂ e : List RealBlock) (hm : realRank d₁ = m + 1) (hn : realRank d₂ = n)
    (μ : ℤ → ℂ) (f : S (m + 1) d₁) (g : S n d₂)
    (φ : 𝓓((⊤ : Opens (Matrix (Fin (m + 1)) (Fin n) ℝ)), ℂ)),
    (∀ (he : realRank e = m + 1), p + 1 < m + 1 →
      ∀ (T : D (n + m + 1) (d₂ ++ d₁) →L[ℂ] D (n + m + 1) (d₂ ++ e))
        (Q : D (m + 1) d₁ →L[ℂ] D (m + 1) e),
        IsSmoothBlockFourierMultiplier (n + p) μ T → IsSmoothBlockFourierMultiplier p μ Q →
        T (smoothSectionVector hm hn f g φ) =
          smoothSectionVector he hn ((derivativeEquiv e).symm (Q (derivativeEquiv d₁ f))) g φ) ∧
    (∀ (he : realRank e = n), p + 1 < n →
      ∀ (T : D (n + m + 1) (d₂ ++ d₁) →L[ℂ] D (n + m + 1) (e ++ d₁))
        (Q : D n d₂ →L[ℂ] D n e),
        IsSmoothBlockFourierMultiplier p μ T → IsSmoothBlockFourierMultiplier p μ Q →
        T (smoothSectionVector hm hn f g φ) =
          smoothSectionVector hm he f ((derivativeEquiv e).symm (Q (derivativeEquiv d₂ g))) φ)

theorem realParabolicSectionMultiplier : RealParabolicSectionMultiplierStatement := by
  intro m n p d₁ d₂ e hm hn μ f g φ
  exact ⟨fun he hp T Q hT hQ => smoothSectionVector_multiplier_first hm hn he hp μ T Q hT hQ f g φ,
    fun he hp T Q hT hQ => smoothSectionVector_multiplier_second hm hn he hp μ T Q hT hQ f g φ⟩

end Langlands.Global.RankinSelbergGlobal.RealParabolicCompactSection
