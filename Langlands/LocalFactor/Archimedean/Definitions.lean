import Langlands.LocalFactor.Analytic.ReciprocalEntire
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-! Explicit archimedean Gamma factors, with poles retained as singular germs. -/

noncomputable section

namespace Langlands.LocalFactor.Archimedean

open scoped Topology

/-- The real archimedean factor `π^(-s/2) Γ(s/2)`, represented by its entire
reciprocal denominator. Evaluation is restricted to regular points. -/
def gammaReal : ReciprocalEntire where
  denominator := fun s => (Complex.Gammaℝ s)⁻¹
  entire := Complex.differentiable_Gammaℝ_inv
  nonzero := ⟨1, by simp⟩

/-- The complex archimedean factor `2 (2π)^(-s) Γ(s)`, including the factor `2`
in Tate's normalization, represented by its entire reciprocal denominator. -/
def gammaComplex : ReciprocalEntire where
  denominator := fun s => (Complex.Gammaℂ s)⁻¹
  entire := Complex.differentiable_Gammaℂ_inv
  nonzero := ⟨1, by simp [Real.pi_ne_zero]⟩

theorem gammaReal_isPole (s : ℂ) :
    gammaReal.IsPole s ↔ ∃ n : ℕ, s = -(2 * (n : ℂ)) := by
  simp only [ReciprocalEntire.IsPole, gammaReal, inv_eq_zero, Complex.Gammaℝ_eq_zero_iff]

theorem gammaComplex_isPole (s : ℂ) :
    gammaComplex.IsPole s ↔ ∃ n : ℕ, s = -(n : ℂ) := by
  simp [ReciprocalEntire.IsPole, gammaComplex, Complex.Gammaℂ_def,
    Complex.Gamma_eq_zero_iff, Real.pi_ne_zero]

theorem gammaReal_eval (s : gammaReal.RegularPoint) :
    (gammaReal.eval s : ℂ) = (Real.pi : ℂ) ^ (-s.val / 2) * Complex.Gamma (s.val / 2) := by
  simp [ReciprocalEntire.eval, gammaReal, Complex.Gammaℝ_def]

theorem gammaComplex_eval (s : gammaComplex.RegularPoint) :
    (gammaComplex.eval s : ℂ) =
      2 * (2 * (Real.pi : ℂ)) ^ (-s.val) * Complex.Gamma s.val := by
  simp [ReciprocalEntire.eval, gammaComplex, Complex.Gammaℂ_def]

/-- An analytic Gamma block and its spectral translation. This is analytic
input data, not an asserted classification of archimedean Weil representations. -/
inductive GammaBlock where
  | real (shift : ℂ)
  | complex (shift : ℂ)

namespace GammaBlock

/-- The actual shifted Gamma factor attached to an analytic block. -/
def factor : GammaBlock → ReciprocalEntire
  | .real a => gammaReal.shift a
  | .complex a => gammaComplex.shift a

theorem real_isPole (a s : ℂ) :
    (factor (.real a)).IsPole s ↔ ∃ n : ℕ, s + a = -(2 * (n : ℂ)) :=
  gammaReal_isPole (s + a)

theorem complex_isPole (a s : ℂ) :
    (factor (.complex a)).IsPole s ↔ ∃ n : ℕ, s + a = -(n : ℂ) :=
  gammaComplex_isPole (s + a)

end GammaBlock

/-- A finite product of actual shifted Gamma factors, retaining every pole.
Attachment to actual Weil representations is a separate construction. -/
def gammaProduct (blocks : List GammaBlock) : ReciprocalEntire :=
  ReciprocalEntire.product (blocks.map GammaBlock.factor)

theorem gammaProduct_isPole (blocks : List GammaBlock) (s : ℂ) :
    (gammaProduct blocks).IsPole s ↔ ∃ b ∈ blocks, b.factor.IsPole s := by
  simp only [gammaProduct, ReciprocalEntire.isPole_product, List.mem_map]
  constructor
  · rintro ⟨F, ⟨b, hb, rfl⟩, hp⟩
    exact ⟨b, hb, hp⟩
  · rintro ⟨b, hb, hp⟩
    exact ⟨b.factor, ⟨b, hb, rfl⟩, hp⟩

theorem gammaProduct_perm {blocks blocks' : List GammaBlock} (h : blocks.Perm blocks') :
    gammaProduct blocks = gammaProduct blocks' :=
  ReciprocalEntire.product_perm (h.map GammaBlock.factor)

/-- A real spectral component in Tate's notation `x^(-N) ω_(s+a)`, with
`N = 0` or `1`. The parity affects epsilon, but not this Gamma factor. -/
def realTateL (_parity : Fin 2) (a : ℂ) : ReciprocalEntire := gammaReal.shift a

/-- A complex spectral component in Tate's notation `z^(-N) ω_(s+a)`,
with `N ≥ 0` and a chosen embedding. -/
def complexTateL (_weight : ℕ) (a : ℂ) : ReciprocalEntire := gammaComplex.shift a

/-- Tate's real abelian epsilon expression for `ψ(x)=exp(2πix)` and
Lebesgue measure, in the component `x^(-N) ω_s`. -/
def realTateEpsilon (parity : Fin 2) : ℂ := Complex.I ^ parity.val

/-- Tate's complex abelian epsilon expression for `ψ(z)=exp(2πi Tr(z))`
and measure `2 da db`, in the component `z^(-N) ω_s`. -/
def complexTateEpsilon (weight : ℕ) : ℂ := Complex.I ^ weight

theorem realTateEpsilon_ne_zero (parity : Fin 2) : realTateEpsilon parity ≠ 0 :=
  pow_ne_zero _ Complex.I_ne_zero

theorem complexTateEpsilon_ne_zero (weight : ℕ) : complexTateEpsilon weight ≠ 0 :=
  pow_ne_zero _ Complex.I_ne_zero

end Langlands.LocalFactor.Archimedean
