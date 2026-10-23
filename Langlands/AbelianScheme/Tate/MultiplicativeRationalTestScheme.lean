import Langlands.AbelianScheme.Tate.RationalTestScheme
import Langlands.AbelianScheme.Tate.MultiplicativeTestScheme
import Langlands.AbelianScheme.Tate.MultiplicativeAwayRational

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme.Gm.TateComparison
universe u
variable {S : Scheme.{u}} {T T' : Over S} (P : ℕ → Prop) (a : T' ⟶ T)

/-- The rational Gm-to-roots equivalence is natural in the test scheme. -/
theorem rationalEquiv_testRestrict (x : Tate.Rational (Gm S).toGrp T P) :
    rationalEquiv T' P (Tate.rationalTestRestrict (Gm S).toGrp P a x) =
      TateTwist.Divisibility.rationalMap P a.left.appTop.hom (rationalEquiv T P x) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x => simp only [Tate.rationalTestRestrict_tmul, rationalEquiv_tmul,
      TateTwist.Divisibility.rationalMap_tmul, integralEquiv_testRestrict]
  | add x y hx hy => simp_all

/-- The inverse rational equivalence satisfies the same square. -/
theorem rationalEquiv_symm_testRestrict
    (x : TateTwist.Divisibility.Rational Γ(T.left, ⊤) P) :
    (rationalEquiv T' P).symm (TateTwist.Divisibility.rationalMap P a.left.appTop.hom x) =
      Tate.rationalTestRestrict (Gm S).toGrp P a ((rationalEquiv T P).symm x) := by
  apply (rationalEquiv T' P).injective
  rw [LinearEquiv.apply_symm_apply, rationalEquiv_testRestrict,
    LinearEquiv.apply_symm_apply]

/-- The finite-adelic bundles preserve this naturality square. -/
theorem finiteAdeleEquiv_testRestrict (h : Global.RationalProfiniteIntegerAdeleComparison)
    (x : Tate.Rational (Gm S).toGrp T P) :
    finiteAdeleEquiv T' P h (Tate.finiteAdeleTestRestrict (Gm S).toGrp P a h x) =
      TateTwist.Divisibility.finiteAdeleMap P h a.left.appTop.hom (finiteAdeleEquiv T P h x) :=
  rationalEquiv_testRestrict P a x

/-- Naturality for the inverse finite-adelic bundles. -/
theorem finiteAdeleEquiv_symm_testRestrict (h : Global.RationalProfiniteIntegerAdeleComparison)
    (x : TateTwist.Divisibility.Rational Γ(T.left, ⊤) P) :
    (finiteAdeleEquiv T' P h).symm
        (TateTwist.Divisibility.finiteAdeleMap P h a.left.appTop.hom x) =
      Tate.finiteAdeleTestRestrict (Gm S).toGrp P a h ((finiteAdeleEquiv T P h).symm x) :=
  rationalEquiv_symm_testRestrict P a x

variable {h : Global.RationalProfiniteIntegerAdeleComparison} {m : ℕ}
variable (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)

/-- Naturality also retains the coupled away finite-adelic bundles. -/
theorem primeToFiniteAdeleEquiv_testRestrict (x : Tate.RationalAway (Gm S).toGrp T m) :
    primeToFiniteAdeleEquiv T' hAway (Tate.primeToFiniteAdeleTestRestrict (Gm S).toGrp a hAway x) =
      TateTwist.Divisibility.primeToFiniteAdeleMap hAway a.left.appTop.hom
        (primeToFiniteAdeleEquiv T hAway x) :=
  rationalEquiv_testRestrict (fun n => Nat.Coprime n m) a x

/-- The inverse away finite-adelic square uses the same witnesses. -/
theorem primeToFiniteAdeleEquiv_symm_testRestrict
    (x : TateTwist.Divisibility.RationalAway Γ(T.left, ⊤) m) :
    (primeToFiniteAdeleEquiv T' hAway).symm
        (TateTwist.Divisibility.primeToFiniteAdeleMap hAway a.left.appTop.hom x) =
      Tate.primeToFiniteAdeleTestRestrict (Gm S).toGrp a hAway
        ((primeToFiniteAdeleEquiv T hAway).symm x) :=
  rationalEquiv_symm_testRestrict (fun n => Nat.Coprime n m) a x

end Langlands.GroupScheme.Gm.TateComparison
