import Langlands.AbelianScheme.Tate.TestScheme
import Langlands.AbelianScheme.Tate.MultiplicativeDivisibility

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Gm.TateComparison
universe u
variable {S : Scheme.{u}} {T T' : Over S} (P : ℕ → Prop) (a : T' ⟶ T)

/-- The actual integral Gm comparison is natural in the test scheme. -/
theorem integralEquiv_testRestrict (x : Tate.Integral (Gm S).toGrp T P) :
    integralEquiv T' P (Tate.testRestrict (Gm S).toGrp P a x) =
      TateTwist.Divisibility.map P a.left.appTop.hom (integralEquiv T P x) := by
  apply Subtype.ext
  funext n
  exact levelEquiv_restrict a n.val (x.val n)

/-- The inverse comparison satisfies the same naturality square. -/
theorem integralEquiv_symm_testRestrict (x : TateTwist.Divisibility.Integral Γ(T.left, ⊤) P) :
    (integralEquiv T' P).symm (TateTwist.Divisibility.map P a.left.appTop.hom x) =
      Tate.testRestrict (Gm S).toGrp P a ((integralEquiv T P).symm x) := by
  apply (integralEquiv T' P).injective
  rw [LinearEquiv.apply_symm_apply, integralEquiv_testRestrict,
    LinearEquiv.apply_symm_apply]

/-- Naturality retains the away scalar bundle. -/
theorem awayEquiv_testRestrict (m : ℕ) (x : Tate.Away (Gm S).toGrp T m) :
    awayEquiv T' m (Tate.awayTestRestrict (Gm S).toGrp m a x) =
      TateTwist.Divisibility.awayLinearMap m a.left.appTop.hom (awayEquiv T m x) :=
  integralEquiv_testRestrict (fun n => Nat.Coprime n m) a x

/-- The inverse away comparison also commutes with test-scheme restriction. -/
theorem awayEquiv_symm_testRestrict (m : ℕ) (x : TateTwist.Divisibility.Away Γ(T.left, ⊤) m) :
    (awayEquiv T' m).symm (TateTwist.Divisibility.awayLinearMap m a.left.appTop.hom x) =
      Tate.awayTestRestrict (Gm S).toGrp m a ((awayEquiv T m).symm x) :=
  integralEquiv_symm_testRestrict (fun n => Nat.Coprime n m) a x

end Langlands.GroupScheme.Gm.TateComparison
