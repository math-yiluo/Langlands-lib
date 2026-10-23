import Langlands.AbelianScheme.Tate.PrimeTestScheme
import Langlands.AbelianScheme.Tate.MultiplicativePrimeAffine

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme.Gm.TateComparison
universe u
variable {S : Scheme.{u}} {T T' : Over S} (p : ℕ) [Fact p.Prime] (a : T' ⟶ T)

/-- Actual prime-adic Gm comparison is natural in the test scheme. -/
theorem primeIntegralEquiv_testRestrict (x : Tate.PrimeAdic.Integral (Gm S).toGrp T p) :
    primeIntegralEquiv T' p (Tate.PrimeAdic.testRestrict (Gm S).toGrp p a x) =
      TateTwist.map p a.left.appTop.hom (primeIntegralEquiv T p x) := by
  apply Subtype.ext
  funext n
  exact levelEquiv_restrict a (p ^ n) (x.val n)

/-- The inverse prime-adic comparison has the same naturality. -/
theorem primeIntegralEquiv_symm_testRestrict (x : TateTwist.Integral Γ(T.left, ⊤) p) :
    (primeIntegralEquiv T' p).symm (TateTwist.map p a.left.appTop.hom x) =
      Tate.PrimeAdic.testRestrict (Gm S).toGrp p a ((primeIntegralEquiv T p).symm x) := by
  apply (primeIntegralEquiv T' p).injective
  rw [LinearEquiv.apply_symm_apply, primeIntegralEquiv_testRestrict,
    LinearEquiv.apply_symm_apply]

/-- Scalar extension preserves prime-adic comparison naturality. -/
theorem primeRationalEquiv_testRestrict (x : Tate.PrimeAdic.Rational (Gm S).toGrp T p) :
    primeRationalEquiv T' p (Tate.PrimeAdic.rationalTestRestrict (Gm S).toGrp p a x) =
      TateTwist.rationalMap p a.left.appTop.hom (primeRationalEquiv T p x) := by
  have h : (primeIntegralEquiv T' p).toLinearMap.comp
        (Tate.PrimeAdic.testRestrict (Gm S).toGrp p a) =
      (TateTwist.map p a.left.appTop.hom).comp (primeIntegralEquiv T p).toLinearMap :=
    LinearMap.ext (primeIntegralEquiv_testRestrict p a)
  have hq := congrArg (fun k => k.baseChange ℚ_[p]) h
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at hq
  exact LinearMap.congr_fun hq x

/-- The inverse rational prime-adic comparison also commutes with restriction. -/
theorem primeRationalEquiv_symm_testRestrict (x : TateTwist.Rational Γ(T.left, ⊤) p) :
    (primeRationalEquiv T' p).symm (TateTwist.rationalMap p a.left.appTop.hom x) =
      Tate.PrimeAdic.rationalTestRestrict (Gm S).toGrp p a ((primeRationalEquiv T p).symm x) := by
  apply (primeRationalEquiv T' p).injective
  rw [LinearEquiv.apply_symm_apply, primeRationalEquiv_testRestrict,
    LinearEquiv.apply_symm_apply]

end Langlands.GroupScheme.Gm.TateComparison
