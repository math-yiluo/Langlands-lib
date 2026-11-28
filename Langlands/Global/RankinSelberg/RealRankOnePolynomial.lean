import Langlands.Global.RankinSelberg.RankOneOrdinaryNormalizedTests
import Langlands.Global.RankinSelberg.RealOrdinaryPolynomialReduction
import Langlands.LocalFactor.Archimedean.RealTatePolynomialGaussian

/-! # Polynomial normalization of real rank-one Gaussian row tests -/

noncomputable section

open Langlands.LocalFactor.Archimedean Langlands.Archimedean
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal RealEqualPolynomialGeneration
open Langlands.LocalFactor.RealTate (polynomialGaussian polynomialGaussian_apply realTatePolynomialGaussian)

attribute [local instance] archimedeanEquationRealGLMeasurable archimedeanEquationRealGLBorel
  archimedeanEquationRealNMeasurable archimedeanEquationRealNBorel
  archimedeanEquationRealQMeasurable archimedeanEquationRealQBorel

/-- Exact polynomial normalization for equal-rank real character lists with standard Gaussian rows. -/
def RealEqualPolynomialAtRank (r : ℕ) (a : ℝˣ) : Prop :=
  ∀ (cs fs : List RealCharacterData), cs.length = r + 1 → fs.length = r + 1 →
    ∀ D : RealQuotientMeasureData r,
      let ds := cs.map RealBlock.character
      let es := fs.map RealBlock.character
      HasPolynomialOrdinaryNormalizations (gaussianEqualIntegral r ds es a Real.pi D)
        (realPairLFactor ds es)

/-- Exact polynomial normalization for adjacent-rank real character lists. -/
def RealAdjacentPolynomialAtRank (r : ℕ) (a : ℝˣ) : Prop :=
  ∀ (cs fs : List RealCharacterData), cs.length = r + 2 → fs.length = r + 1 →
    ∀ D : RealQuotientMeasureData r,
      let ds := cs.map RealBlock.character
      let es := fs.map RealBlock.character
      HasPolynomialOrdinaryNormalizations (realOrdinaryUnequalTest (Nat.lt_succ_self r) ds es a D)
        (realPairLFactor ds es)

namespace RealRankZero

private theorem exists_polynomialGaussian_eq_lineSchwartz
    {Φ : 𝓢(Fin (0 + 1) → ℝ, ℂ)} (hΦ : IsGaussianPolynomialRow Real.pi Φ) :
    ∃ p : Polynomial ℂ, lineSchwartz Φ = polynomialGaussian p := by
  obtain ⟨P, hP⟩ := hΦ
  let A : MvPolynomial (Fin (0 + 1)) ℂ →+* Polynomial ℂ :=
    MvPolynomial.eval₂Hom Polynomial.C (fun _ => Polynomial.X)
  refine ⟨A P, ?_⟩
  ext x
  have h := hP (fun _ => x)
  change Φ (fun _ => x) = MvPolynomial.eval (fun _ => (x : ℂ)) P *
    (Real.exp (-Real.pi * ∑ _ : Fin (0 + 1), x ^ 2) : ℂ) at h
  have he : (Polynomial.evalRingHom (x : ℂ)).comp A = MvPolynomial.eval (fun _ => (x : ℂ)) := by
    ext <;> simp [A]
  have heval : (A P).eval (x : ℂ) = MvPolynomial.eval (fun _ => (x : ℂ)) P :=
    congrArg (fun H : MvPolynomial (Fin (0 + 1)) ℂ →+* ℂ => H P) he
  rw [lineSchwartz_apply, h, Fin.sum_univ_one, polynomialGaussian_apply, heval, Complex.ofReal_exp]
  push_cast
  rw [neg_mul]

/-- At any nonzero additive scale, a standard Gaussian row gives a polynomial normalized
value for every exact rank-one real equal test. -/
def RealRankOnePolynomialStatement : Prop :=
  ∀ a : ℝˣ, RealEqualPolynomialAtRank 0 a

theorem realRankOnePolynomial : RealRankOnePolynomialStatement := by
  intro a cs fs hcs hfs D
  obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp hcs
  obtain ⟨c', rfl⟩ := List.length_eq_one_iff.mp hfs
  dsimp only [List.map_cons, List.map_nil]
  rintro ⟨W, V, Φ⟩
  obtain ⟨C, hW⟩ := exists_eq_of_mem_realWhittakerModel W.2
  obtain ⟨C', hV⟩ := exists_eq_of_mem_realWhittakerModel V.2
  obtain ⟨κ, _, hκ⟩ := exists_measure_eq D
  obtain ⟨P, hP⟩ := exists_polynomialGaussian_eq_lineSchwartz Φ.2
  let d := c.mul c'
  obtain ⟨Q, hQ⟩ := realTatePolynomialGaussian P d.parity
  let R := Polynomial.C ((κ : ℂ) * (C * C')) * Q.comp (Polynomial.X + Polynomial.C d.exponent)
  refine ⟨⟨R.eval, fun s _ => R.differentiable.analyticAt s, ⟨-d.exponent.re, fun s hs => ?_⟩⟩, R, rfl⟩
  have hpos : 0 < (s + d.exponent).re := by rw [Complex.add_re]; linarith
  change realEqualIntegral D W V Φ.val s = R.eval s *
    ((realPairLFactor [RealBlock.character c] [RealBlock.character c']).denominator s)⁻¹
  rw [equalIntegral_eq c c' hκ hW hV, hP, hQ _ hpos, realPairLFactor_character, inv_inv]
  simp only [R, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, ← add_assoc]
  dsimp only [d]
  ring

end RealRankZero
end Langlands.Global.RankinSelbergGlobal
