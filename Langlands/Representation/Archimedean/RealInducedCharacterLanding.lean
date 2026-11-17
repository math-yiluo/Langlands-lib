import Langlands.Representation.Archimedean.RealSwapFLanding
import Langlands.Representation.Archimedean.RealSwapLandingIntegral

/-!
# Low block modes after two block multipliers on `GL₃(ℝ)`: the mirror case

This module is the mirror of `RealSwapFLanding.highModes_eq_zero`, with the roles of the two
rotations `r_0` and `r_1` exchanged and the standard module of `[d, c]` (induction block first)
as the space of test functions. It assumes `RealSwapLandingInducedFirstStatement`.
-/

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

set_option autoImplicit false

namespace Langlands.Archimedean

namespace RealInducedCharacter

open RealPrincipalSeriesDuality RealBlockFourierFinite RealBlockJacquet RealBlockTransposition
open RealBlockMultiplier RealBlockRotation RealBlockPropagation RealBlockDerivative
open PrincipalSeriesExtension GramFormula RealSwapFLanding
open Langlands.LocalFactor.Archimedean

attribute [local instance] measurableSpaceK

local instance borelSpaceKMirror (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

/-! ## Low modes after two block multipliers -/

/-- **High modes after two block multipliers, mirror case.** Assume the landing statement
`RealSwapLandingInducedFirstStatement`. Let `c`, `d`, `ℓ = |d.weight|`, `δ`, `μ₀`, `μ₁` be as
there (`μ₁` for `δ` on the class `ε₁`, `μ₀` for `δ + ℓ` on the class `ε₀`), and `e ∈ ℕ`. Let
`f, g₁, g, G` be continuous right `O(3)`-finite functions on `GL_3(ℝ)` such that, on `O(3)`:

* `Φ¹_j f = 0` for `|j| ≥ ℓ`;
* `Φ⁰_j g₁ = μ₀ j · Φ⁰_j f` and `Φ¹_j g = μ₁ j · Φ¹_j g₁` for all `j`;
* `Φ⁰_j G = Φ⁰_j g` for `|j| ≥ ℓ` and `Φ⁰_j G = 0` for `|j| < ℓ`;

and such that `G(diag(sgn a) κ) = χ(sgn a) · sgnDet(diag(sgn a))^e · G(κ)` for `a ∈ (ℝˣ)³`,
`κ ∈ O(3)`, where `χ` is the principal series character of the position characters of
`[d, c]`. Then `Φ⁰_j g = 0` on `O(3)` for `|j| ≥ ℓ`. -/
theorem highModes_eq_zero_mirror (hL : RealSwapLandingInducedFirstStatement)
    (c : RealCharacterData) (d : ComplexCharacterData) (δ : ℂ) (μ₀ μ₁ : ℤ → ℂ)
    (hμ₁r : IsRecurrent δ (c.parity.val : ℤ) μ₁)
    (hμ₁s : IsSymmetric (c.parity.val : ℤ) ((-1 : ℂ) ^ c.parity.val) μ₁)
    (hμ₀r : IsRecurrent (δ + (d.weight.natAbs : ℂ))
      ((d.weight.natAbs + 1 + c.parity.val : ℕ) : ℤ) μ₀)
    (hμ₀s : IsSymmetric ((d.weight.natAbs + 1 + c.parity.val : ℕ) : ℤ)
      ((-1 : ℂ) ^ (d.weight.natAbs + 1 + c.parity.val)) μ₀) (e : ℕ)
    {f g₁ g G : Langlands.GeneralLinear 3 ℝ → ℂ}
    (hf : Continuous f) (hg₁ : Continuous g₁) (hg : Continuous g) (hG : Continuous G)
    (hfK : f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear 3 ℝ))
      (unitaryCompact ℝ 3))
    (hg₁K : g₁ ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear 3 ℝ))
      (unitaryCompact ℝ 3))
    (hgK : g ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear 3 ℝ))
      (unitaryCompact ℝ 3))
    (hGK : G ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear 3 ℝ))
      (unitaryCompact ℝ 3))
    (hf1 : ∀ j : ℤ, |d.weight| ≤ |j| → ∀ x ∈ unitaryCompact ℝ 3,
      blockFourierCoefficient 3 1 j f x = 0)
    (h₀ : ∀ j : ℤ, ∀ x ∈ unitaryCompact ℝ 3,
      blockFourierCoefficient 3 0 j g₁ x = μ₀ j * blockFourierCoefficient 3 0 j f x)
    (h₁ : ∀ j : ℤ, ∀ x ∈ unitaryCompact ℝ 3,
      blockFourierCoefficient 3 1 j g x = μ₁ j * blockFourierCoefficient 3 1 j g₁ x)
    (hGhigh : ∀ j : ℤ, |d.weight| ≤ |j| → ∀ x ∈ unitaryCompact ℝ 3,
      blockFourierCoefficient 3 0 j G x = blockFourierCoefficient 3 0 j g x)
    (hGlow : ∀ j : ℤ, |j| < |d.weight| → ∀ x ∈ unitaryCompact ℝ 3,
      blockFourierCoefficient 3 0 j G x = 0)
    (hGM : ∀ (a : Fin 3 → ℝˣ) (κ : Matrix.unitaryGroup (Fin 3) ℝ),
      G (Unitary.toUnits (signDiagonal (fun i => (a i : ℝ)) * κ)) =
        principalSeriesCharacter ℝ 3
            (realPositionCharacter [RealBlock.induced d, RealBlock.character c])
            (fun i => signUnit (a i)) *
          sgnDet 3 (Unitary.toUnits (signDiagonal (fun i => (a i : ℝ)))) ^ e *
            G (Unitary.toUnits κ)) :
    ∀ j : ℤ, |d.weight| ≤ |j| → ∀ x ∈ unitaryCompact ℝ 3,
      blockFourierCoefficient 3 0 j g x = 0 := by
  have hp0 : (0 : ℕ) + 1 < 3 := by norm_num
  have hp1 : (1 : ℕ) + 1 < 3 := by norm_num
  have habs : |d.weight| = (d.weight.natAbs : ℤ) := Int.abs_eq_natAbs d.weight
  -- the twisted projection `G' = G · sgnDet^e` and the function `φ = conj ∘ G'` on `O(3)`
  set G' : Langlands.GeneralLinear 3 ℝ → ℂ := fun x => G x * sgnDet 3 x ^ e with hG'def
  have hG'c : Continuous G' := continuous_mul_sgnDet_pow hG e
  have hG'K := mem_kFiniteVectors_mul_sgnDet_pow hGK e
  obtain ⟨P, hP⟩ :=
    OrthogonalFinitePolynomial.exists_mvPolynomial_of_mem_kFiniteVectors hG'c hG'K 1
  set φ : Matrix.unitaryGroup (Fin 3) ℝ → ℂ := fun κ => conj (G' (Unitary.toUnits κ))
    with hφdef
  have hφP : ∀ κ : Matrix.unitaryGroup (Fin 3) ℝ, φ κ = MvPolynomial.eval
      (fun ij => (((κ : Matrix (Fin 3) (Fin 3) ℝ) ij.1 ij.2 : ℝ) : ℂ))
        (MvPolynomial.map (starRingEnd ℂ) P) := by
    intro κ
    rw [hφdef]
    simp only
    rw [← one_mul (Unitary.toUnits κ), hP κ]
    exact JacquetKernel.conj_eval_ofReal P (fun ij => (κ : Matrix (Fin 3) (Fin 3) ℝ) ij.1 ij.2)
  have hφc : Continuous φ :=
    Complex.continuous_conj.comp (hG'c.comp continuous_unitary_toUnits)
  have hfin : FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun k : Matrix.unitaryGroup (Fin 3) ℝ => fun x => φ (x * k))) := by
    have h := TranslateFinite.finiteDimensional_span_eval (n := 3)
      (MvPolynomial.map (starRingEnd ℂ) P)
    have heq : (fun k : Matrix.unitaryGroup (Fin 3) ℝ => fun x => φ (x * k)) =
        fun k x => MvPolynomial.eval (fun ij => (((x * k : Matrix.unitaryGroup (Fin 3) ℝ) :
          Matrix (Fin 3) (Fin 3) ℝ) ij.1 ij.2 : ℂ)) (MvPolynomial.map (starRingEnd ℂ) P) :=
      funext fun k => funext fun x => hφP (x * k)
    rw [heq]
    exact h
  have hφM : ∀ (a : Fin 3 → ℝˣ) (κ : Matrix.unitaryGroup (Fin 3) ℝ),
      φ (signDiagonal (fun i => (a i : ℝ)) * κ) =
        principalSeriesCharacter ℝ 3
          (realPositionCharacter [RealBlock.induced d, RealBlock.character c])
          (fun i => signUnit (a i)) * φ κ := by
    intro a κ
    have key : G' (Unitary.toUnits (signDiagonal (fun i => (a i : ℝ)) * κ)) =
        principalSeriesCharacter ℝ 3
          (realPositionCharacter [RealBlock.induced d, RealBlock.character c])
          (fun i => signUnit (a i)) * G' (Unitary.toUnits κ) := by
      simp only [hG'def]
      rw [hGM, MonoidHom.map_mul, sgnDet_mul, mul_pow]
      linear_combination (principalSeriesCharacter ℝ 3
          (realPositionCharacter [RealBlock.induced d, RealBlock.character c])
          (fun i => signUnit (a i)) * G (Unitary.toUnits κ) *
            sgnDet 3 (Unitary.toUnits κ) ^ e) *
        sgnDet_pow_mul_self e (Unitary.toUnits (signDiagonal (fun i => (a i : ℝ))))
    simp only [hφdef]
    rw [key, map_mul, conj_principalSeriesCharacter_signUnit]
  -- the test function `t ∈ [d, c]` with `t = conj G'` on `O(3)`
  obtain ⟨t, htK, htval⟩ := principalSeriesExtension 3
    [RealBlock.induced d, RealBlock.character c] φ hφc hfin hφM
  have htc : Continuous t := JacquetKernel.continuous_of_mem htK
  have hval : ∀ x ∈ unitaryCompact ℝ 3, t x = conj (G' x) := by
    intro x hx
    have hk : x = Unitary.toUnits
        (⟨(x : Matrix (Fin 3) (Fin 3) ℝ), hx⟩ : Matrix.unitaryGroup (Fin 3) ℝ) := Units.ext rfl
    rw [hk, htval]
  have htlow : ∀ j : ℤ, |j| < |d.weight| → ∀ x ∈ unitaryCompact ℝ 3,
      blockFourierCoefficient 3 0 j t x = 0 := by
    intro j hj x hx
    rw [blockFourierCoefficient_congr hval 0 j hx, blockFourierCoefficient_conj, hG'def,
      blockFourierCoefficient_mul_sgnDet_pow, hGlow (-j) (by rwa [abs_neg]) x hx, mul_zero,
      map_zero]
  have htmem : t ∈ kFiniteFunctions
      (realStandardModule 3 [RealBlock.induced d, RealBlock.character c]) (unitaryCompact ℝ 3) :=
    ⟨RealSwapLandingIntegral.mem_realStandardModule_induced_character d c htK.1 htlow, htK.2⟩
  -- the reflected multipliers applied to `t`, and the landing statement
  obtain ⟨t₀, ht₀c, ht₀K, ht₀⟩ := exists_multiplier hp1 htc htK.2 (fun j => μ₁ (-j))
  obtain ⟨u, huc, huK, hu⟩ := exists_multiplier hp0 ht₀c ht₀K (fun j => μ₀ (-j))
  have hland := hL c d δ (fun j => μ₀ (-j)) (fun j => μ₁ (-j)) t t₀ u
    (isRecurrent_comp_neg hμ₁r) (isSymmetric_comp_neg (neg_one_pow_mul_self _) hμ₁s)
    (isRecurrent_comp_neg hμ₀r) (isSymmetric_comp_neg (neg_one_pow_mul_self _) hμ₀s) htmem
    ht₀c huc (fun x hx k => ht₀ k x hx) (fun x hx k => hu k x hx)
  -- the twisted test functions
  have hψc := continuous_mul_sgnDet_pow htc e
  have hψ₀c := continuous_mul_sgnDet_pow ht₀c e
  have hψ₁c := continuous_mul_sgnDet_pow huc e
  have hψK := mem_kFiniteVectors_mul_sgnDet_pow htK.2 e
  have hψ₀K := mem_kFiniteVectors_mul_sgnDet_pow ht₀K e
  have hψ₁K := mem_kFiniteVectors_mul_sgnDet_pow huK e
  -- `∫ g ψ = ∫ g₁ ψ₀ = ∫ f ψ₁ = 0`
  have i₁ := integral_mul_eq_of_multiplier hp1 hg₁ hg hψc hψ₀c hg₁K hgK hψK hψ₀K μ₁ h₁
    (fun j x hx => by
      rw [blockFourierCoefficient_mul_sgnDet_pow, blockFourierCoefficient_mul_sgnDet_pow,
        ht₀ j x hx]
      ring)
  have i₂ := integral_mul_eq_of_multiplier hp0 hf hg₁ hψ₀c hψ₁c hfK hg₁K hψ₀K hψ₁K μ₀ h₀
    (fun j x hx => by
      rw [blockFourierCoefficient_mul_sgnDet_pow, blockFourierCoefficient_mul_sgnDet_pow,
        hu j x hx]
      ring)
  have i₃ := integral_mul_eq_zero_of_modes hp1 hψ₁c hf hψ₁K hfK d.weight.natAbs
    (fun j hj x hx => by
      rw [blockFourierCoefficient_mul_sgnDet_pow, hland x hx j (habs ▸ hj), mul_zero])
    (fun j hj x hx => hf1 j (habs ▸ hj) x hx)
  -- `∫ G ψ = ∫ g ψ` by the transposition with the indicator of the high modes
  have i₄ := integral_mul_eq_of_multiplier hp0 hg hG hψc hψc hgK hGK hψK hψK
    (fun j => if |d.weight| ≤ |j| then 1 else 0)
    (fun j x hx => by
      by_cases hj : |d.weight| ≤ |j|
      · rw [ite_eq_left hj, one_mul, hGhigh j hj x hx]
      · rw [ite_eq_right hj, zero_mul, hGlow j (not_le.mp hj) x hx])
    (fun j x hx => by
      rw [abs_neg]
      by_cases hj : |d.weight| ≤ |j|
      · rw [ite_eq_left hj, one_mul]
      · rw [ite_eq_right hj, zero_mul, blockFourierCoefficient_mul_sgnDet_pow,
          htlow j (not_le.mp hj) x hx, mul_zero])
  -- `ψ = conj G` on `O(3)`
  have hψG : ∀ x ∈ unitaryCompact ℝ 3, t x * sgnDet 3 x ^ e = conj (G x) := by
    intro x hx
    rw [hval x hx]
    simp only [hG'def, map_mul, map_pow, conj_sgnDet]
    rw [mul_assoc, sgnDet_pow_mul_self, mul_one]
  have hint : ∫ k, G (k : Langlands.GeneralLinear 3 ℝ) *
      conj (G (k : Langlands.GeneralLinear 3 ℝ)) ∂haarK 3 = 0 := by
    calc ∫ k, G (k : Langlands.GeneralLinear 3 ℝ) * conj (G (k : Langlands.GeneralLinear 3 ℝ))
          ∂haarK 3
        = ∫ k, G (k : Langlands.GeneralLinear 3 ℝ) *
            (t (k : Langlands.GeneralLinear 3 ℝ) *
              sgnDet 3 (k : Langlands.GeneralLinear 3 ℝ) ^ e) ∂haarK 3 :=
          integral_congr_ae (Filter.Eventually.of_forall fun k => by beta_reduce; rw [hψG _ k.2])
      _ = _ := i₄
      _ = _ := i₁
      _ = _ := i₂
      _ = ∫ k, (u (k : Langlands.GeneralLinear 3 ℝ) *
            sgnDet 3 (k : Langlands.GeneralLinear 3 ℝ) ^ e) *
              f (k : Langlands.GeneralLinear 3 ℝ) ∂haarK 3 :=
          integral_congr_ae (Filter.Eventually.of_forall fun k => mul_comm _ _)
      _ = 0 := i₃
  have hG0 : ∀ x ∈ unitaryCompact ℝ 3, G x = (fun _ => (0 : ℂ)) x :=
    fun x hx => eq_zero_of_integral_mul_conj hG hint hx
  intro j hj x hx
  rw [← hGhigh j hj x hx, blockFourierCoefficient_congr hG0 0 j hx]
  simp [blockFourierCoefficient]

end RealInducedCharacter

end Langlands.Archimedean
