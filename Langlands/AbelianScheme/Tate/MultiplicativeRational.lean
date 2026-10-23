import Langlands.AbelianScheme.Tate.MultiplicativeDivisibility
import Langlands.AbelianScheme.Tate.TwistRationalScalars

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.Gm.TateComparison
universe u
variable {S : Scheme.{u}} (T : Over S) (P : ℕ → Prop)

/-- Rationalization of the actual selected Gm torsion-to-roots equivalence. -/
def rationalEquiv :
    Tate.Rational (Gm S).toGrp T P ≃ₗ[ℚ]
      TateTwist.Divisibility.Rational Γ(T.left, ⊤) P :=
  (integralEquiv T P).toAddEquiv.toIntLinearEquiv.baseChange ℤ ℚ _ _

@[simp] theorem rationalEquiv_tmul (q : ℚ) (x : Tate.Integral (Gm S).toGrp T P) :
    rationalEquiv T P (q ⊗ₜ[ℤ] x) = q ⊗ₜ[ℤ] integralEquiv T P x := rfl

@[simp] theorem rationalEquiv_symm_tmul (q : ℚ)
    (x : TateTwist.Divisibility.Integral Γ(T.left, ⊤) P) :
    (rationalEquiv T P).symm (q ⊗ₜ[ℤ] x) = q ⊗ₜ[ℤ] (integralEquiv T P).symm x := rfl

@[simp] theorem rationalEquiv_toRational (x : Tate.Integral (Gm S).toGrp T P) :
    rationalEquiv T P (Tate.toRational (Gm S).toGrp T P x) =
      TateTwist.Divisibility.toRational Γ(T.left, ⊤) P (integralEquiv T P x) := rfl

/-- Rationalization retains the actual full residue scalar action. -/
theorem rationalEquiv_scalarAction (a : ℚ ⊗[ℤ] Global.ProfiniteIntegerRing)
    (x : Tate.Rational (Gm S).toGrp T P) :
    rationalEquiv T P (Tate.rationalScalarAction (Gm S).toGrp T P a x) =
      TateTwist.Divisibility.rationalScalarAction Γ(T.left, ⊤) P a (rationalEquiv T P x) :=
  TateScalarExtension.map_action (integralEquiv T P).toLinearMap a x

/-- The same comparison is compatible with both transported finite-adelic actions. -/
theorem rationalEquiv_finiteAdeleAction (h : Global.RationalProfiniteIntegerAdeleComparison)
    (a : Global.FiniteAdeles ℚ) (x : Tate.Rational (Gm S).toGrp T P) :
    rationalEquiv T P (Tate.finiteAdeleAction (Gm S).toGrp T P h a x) =
      TateTwist.Divisibility.finiteAdeleAction Γ(T.left, ⊤) P h a (rationalEquiv T P x) :=
  rationalEquiv_scalarAction T P _ x

/-- The selected comparison bundled as finite-adelic linear, with an explicit hypothesis. -/
def finiteAdeleEquiv (h : Global.RationalProfiniteIntegerAdeleComparison) :
    let := Tate.finiteAdeleModule (Gm S).toGrp T P h
    let := TateTwist.Divisibility.finiteAdeleModule Γ(T.left, ⊤) P h
    Tate.Rational (Gm S).toGrp T P ≃ₗ[Global.FiniteAdeles ℚ]
      TateTwist.Divisibility.Rational Γ(T.left, ⊤) P := by
  let := Tate.finiteAdeleModule (Gm S).toGrp T P h
  let := TateTwist.Divisibility.finiteAdeleModule Γ(T.left, ⊤) P h
  exact { (rationalEquiv T P).toAddEquiv with
    map_smul' := rationalEquiv_finiteAdeleAction T P h }

@[simp] theorem finiteAdeleEquiv_apply (h : Global.RationalProfiniteIntegerAdeleComparison)
    (x : Tate.Rational (Gm S).toGrp T P) :
    finiteAdeleEquiv T P h x = rationalEquiv T P x := rfl

/-- The full rational comparison is the selection of every positive order. -/
abbrev fullRationalEquiv :
    Tate.RationalFull (Gm S).toGrp T ≃ₗ[ℚ]
      TateTwist.Divisibility.RationalFull Γ(T.left, ⊤) :=
  rationalEquiv T (fun _ => True)

variable (m : ℕ)

/-- The away rational comparison retains exactly the orders coprime to the modulus. -/
abbrev awayRationalEquiv :
    Tate.RationalAway (Gm S).toGrp T m ≃ₗ[ℚ]
      TateTwist.Divisibility.RationalAway Γ(T.left, ⊤) m :=
  rationalEquiv T (fun n => Nat.Coprime n m)

/-- It also retains the actual away residue scalar action. -/
theorem awayRationalEquiv_scalarAction (a : ℚ ⊗[ℤ] Global.PrimeToProfiniteIntegerRing m)
    (x : Tate.RationalAway (Gm S).toGrp T m) :
    awayRationalEquiv T m (Tate.rationalAwayScalarAction (Gm S).toGrp T m a x) =
      TateTwist.Divisibility.rationalAwayScalarAction Γ(T.left, ⊤) m a
        (awayRationalEquiv T m x) :=
  TateScalarExtension.map_action (awayEquiv T m).toLinearMap a x

/-- Rationalization preserves the full-to-away comparison square. -/
theorem awayRationalEquiv_restrictAway (x : Tate.RationalFull (Gm S).toGrp T) :
    awayRationalEquiv T m (Tate.rationalRestrictAway (Gm S).toGrp T m x) =
      TateTwist.Divisibility.rationalRestrictAway Γ(T.left, ⊤) m (fullRationalEquiv T x) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x => rfl
  | add x y hx hy => simp_all

/-- The inverse rational comparison preserves the same restriction square. -/
theorem awayRationalEquiv_symm_restrictAway
    (x : TateTwist.Divisibility.RationalFull Γ(T.left, ⊤)) :
    (awayRationalEquiv T m).symm
        (TateTwist.Divisibility.rationalRestrictAway Γ(T.left, ⊤) m x) =
      Tate.rationalRestrictAway (Gm S).toGrp T m ((fullRationalEquiv T).symm x) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x => rfl
  | add x y hx hy => simp_all

end Langlands.GroupScheme.Gm.TateComparison
