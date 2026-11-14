import Langlands.Automorphic.AssociatedGammaLocalLink
import Langlands.Global.Factors.RelativeWeilFunctionalEquationStatement
import Langlands.Correspondence.SupercuspidalGammaCompatibility
import Langlands.Correspondence.SegmentEpsilonAlgebra
import Langlands.WeilDeligne.TensorDual

/-!
# The gamma factor of arithmetic local factors

If `f` is a factor triple of a pair `(X, Y)` of Weil–Deligne classes with the dual pair
`(X^∨, Y^∨)` (`IsArithmeticPairLocalFactors`), its gamma factor `ε(s) L∨(1 - s) / L(s)` has a
rational continuation that is an arithmetic pair gamma factor of `(X, Y)`.
-/

noncomputable section

set_option autoImplicit false

open Polynomial

universe u uV uE

namespace Langlands.Global.FunctionalEquationComparison

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{u} p}

/-- The gamma factor of arithmetic local factors continues an arithmetic pair gamma factor. -/
theorem IsArithmeticPairLocalFactors.exists_gamma
    {eC : LocalFactor.CommonClosure.ReciprocityFamily K}
    {ε : LocalFactor.NonabelianSystem.Assignment.{u, uE} K}
    {hε : LocalFactor.NonabelianSystem.IsSystem K eC ε}
    {ψ : Correspondence.NontrivialAdditiveCharacter K}
    {B B' : Weil.Local.LocalWeilDeligneRepresentation.{u, uV} K} {f : LocalFactors}
    (hf : IsArithmeticPairLocalFactors.{u, uV, uE} K eC ε hε ψ
      (WeilDeligneRepresentation.classOf B) (WeilDeligneRepresentation.classOf B')
      (WeilDeligneRepresentation.dualClass (WeilDeligneRepresentation.classOf B))
      (WeilDeligneRepresentation.dualClass (WeilDeligneRepresentation.classOf B')) f) :
    ∃ H : RatFunc ℂ, Correspondence.IsArithmeticPairGammaFactor K eC ε hε ψ
        (WeilDeligneRepresentation.classOf B) (WeilDeligneRepresentation.classOf B') H ∧
      RankinSelberg.HasRationalContinuation K.canonicalTopologicalData.residueCardinality
        f.gamma H := by
  obtain ⟨hL, hLd, c, m, he, hεf⟩ := hf
  set q := K.canonicalTopologicalData.residueCardinality with hq_def
  have hq : 1 < q := K.canonicalTopologicalData.residueCardinality_gt_one
  set I := Weil.Local.localInertia K
  set g := Weil.Local.localGeometricFrobenius K
  set T := WeilDeligneRepresentation.tensor B B'
  set P := LocalFactor.WeilDeligne.eulerPolynomial T I g with hP_def
  set Pd := LocalFactor.WeilDeligne.eulerPolynomial (WeilDeligneRepresentation.dual T) I g
    with hPd_def
  have hLeq : ∀ s, f.lFactor s = RatFunc.eval (RingHom.id ℂ) (RankinSelberg.spectralPoint q s)
      ((algebraMap ℂ[X] (RatFunc ℂ) P)⁻¹) := hL
  have hLdeq : ∀ s, f.dualLFactor s = RatFunc.eval (RingHom.id ℂ)
      (RankinSelberg.spectralPoint q s) ((algebraMap ℂ[X] (RatFunc ℂ) Pd)⁻¹) := by
    intro s
    rw [hLd s]
    congr 1
    change LocalFactor.WeilDeligne.rationalLFactor
        (WeilDeligneRepresentation.tensor (WeilDeligneRepresentation.dual B)
          (WeilDeligneRepresentation.dual B')) I g =
      LocalFactor.WeilDeligne.rationalLFactor (WeilDeligneRepresentation.dual T) I g
    exact LocalFactor.WeilDeligne.rationalLFactor_eq_of_equiv I
      (WeilDeligneRepresentation.tensorDualEquiv B B') g
  have hPne : P ≠ 0 := fun h => by
    have := LocalFactor.WeilDeligne.eulerPolynomial_coeff_zero T I g
    rw [← hP_def, h, Polynomial.coeff_zero] at this
    exact zero_ne_one this
  have hPdne : Pd ≠ 0 := fun h => by
    have := LocalFactor.WeilDeligne.eulerPolynomial_coeff_zero
      (WeilDeligneRepresentation.dual T) I g
    rw [← hPd_def, h, Polynomial.coeff_zero] at this
    exact zero_ne_one this
  have hH : ((RankinSelberg.rationalEpsilonMonomial c m : RankinSelberg.RationalFunctions) *
      LocalFactor.WeilDeligne.rationalLRatioClass I g (LocalFactor.residueReflection K)
        (WeilDeligneRepresentation.tensorClass (WeilDeligneRepresentation.classOf B)
          (WeilDeligneRepresentation.classOf B'))) =
      RankinSelberg.rationalGammaExpression (LocalFactor.residueReflection K) c m P Pd := by
    change _ * LocalFactor.WeilDeligne.rationalLRatio T I g _ = _
    rw [LocalFactor.WeilDeligne.rationalLRatio_eq, RankinSelberg.rationalGammaExpression,
      mul_div_assoc]
  refine ⟨_, ⟨c, m, he, rfl⟩, ?_⟩
  rw [hH]
  obtain ⟨a, ha⟩ := RankinSelberg.hasRationalContinuation_polynomialGammaExpression hq
    (LocalFactor.coe_residueReflection K) c m P Pd hPdne
  obtain ⟨σ₁, h₁⟩ := RankinSelberg.eval_spectralPoint_ne_zero_of_ne_zero hq hPne
  obtain ⟨σ₂, h₂⟩ := RankinSelberg.eval_spectralPoint_one_sub_ne_zero hq hPdne
  refine ⟨max a (max σ₁ σ₂), fun s hs => ?_⟩
  have hsa : a < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have hs₁ : σ₁ < s.re := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hs
  have hs₂ : σ₂ < s.re := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hs
  refine ⟨(ha s hsa).1, ?_⟩
  rw [← (ha s hsa).2]
  have hev : ∀ (R : ℂ[X]) (z : ℂ), R.eval z ≠ 0 →
      RatFunc.eval (RingHom.id ℂ) z ((algebraMap ℂ[X] (RatFunc ℂ) R)⁻¹) = (R.eval z)⁻¹ := by
    intro R z hz
    have h0 : RatFunc.eval (RingHom.id ℂ) z (algebraMap ℂ[X] (RatFunc ℂ) R) = R.eval z := by
      rw [RatFunc.eval_algebraMap]
      simp
    rw [RankinSelberg.RationalEvaluation.eval_inv (by rw [h0]; exact hz), h0]
  change f.epsilonFactor s * f.dualLFactor (1 - s) / f.lFactor s = _
  rw [hεf s, hLeq s, hLdeq (1 - s), hev P _ (h₁ s hs₁), hev Pd _ (h₂ s hs₂)]
  rfl

end Langlands.Global.FunctionalEquationComparison
