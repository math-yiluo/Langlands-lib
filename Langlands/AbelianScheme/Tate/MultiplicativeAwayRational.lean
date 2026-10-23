import Langlands.AbelianScheme.Tate.MultiplicativeRational
import Langlands.AbelianScheme.Tate.TwistAwayRationalScalars

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.Gm.TateComparison
universe u
variable {S : Scheme.{u}} (T : Over S) {m : ℕ}

variable {h : Global.RationalProfiniteIntegerAdeleComparison}
variable (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)

/-- Both away finite-adelic actions use the same explicitly assumed scalar comparison. -/
theorem awayRationalEquiv_primeToFiniteAdeleAction
    (a : Global.PrimeToFiniteAdeles m) (x : Tate.RationalAway (Gm S).toGrp T m) :
    awayRationalEquiv T m (Tate.primeToFiniteAdeleAction (Gm S).toGrp T hAway a x) =
      TateTwist.Divisibility.primeToFiniteAdeleAction Γ(T.left, ⊤) hAway a
        (awayRationalEquiv T m x) :=
  awayRationalEquiv_scalarAction T m _ x

/-- The away comparison bundled as linear over the away finite adeles. -/
def primeToFiniteAdeleEquiv :
    let := Tate.primeToFiniteAdeleModule (Gm S).toGrp T hAway
    let := TateTwist.Divisibility.primeToFiniteAdeleModule Γ(T.left, ⊤) hAway
    Tate.RationalAway (Gm S).toGrp T m ≃ₗ[Global.PrimeToFiniteAdeles m]
      TateTwist.Divisibility.RationalAway Γ(T.left, ⊤) m := by
  let := Tate.primeToFiniteAdeleModule (Gm S).toGrp T hAway
  let := TateTwist.Divisibility.primeToFiniteAdeleModule Γ(T.left, ⊤) hAway
  exact { (awayRationalEquiv T m).toAddEquiv with
    map_smul' := awayRationalEquiv_primeToFiniteAdeleAction T hAway }

@[simp] theorem primeToFiniteAdeleEquiv_apply (x : Tate.RationalAway (Gm S).toGrp T m) :
    primeToFiniteAdeleEquiv T hAway x = awayRationalEquiv T m x := rfl


@[simp] theorem primeToFiniteAdeleEquiv_tmul (q : ℚ)
    (x : Tate.Away (Gm S).toGrp T m) :
    primeToFiniteAdeleEquiv T hAway (q ⊗ₜ[ℤ] x) = q ⊗ₜ[ℤ] awayEquiv T m x := rfl

@[simp] theorem primeToFiniteAdeleEquiv_symm_tmul (q : ℚ)
    (x : TateTwist.Divisibility.Away Γ(T.left, ⊤) m) :
    (primeToFiniteAdeleEquiv T hAway).symm (q ⊗ₜ[ℤ] x) =
      q ⊗ₜ[ℤ] (awayEquiv T m).symm x := rfl

/-- The inverse equivalence intertwines the same away finite-adelic actions. -/
theorem primeToFiniteAdeleEquiv_symm_action (a : Global.PrimeToFiniteAdeles m)
    (x : TateTwist.Divisibility.RationalAway Γ(T.left, ⊤) m) :
    (primeToFiniteAdeleEquiv T hAway).symm
        (TateTwist.Divisibility.primeToFiniteAdeleAction Γ(T.left, ⊤) hAway a x) =
      Tate.primeToFiniteAdeleAction (Gm S).toGrp T hAway a
        ((primeToFiniteAdeleEquiv T hAway).symm x) := by
  apply (primeToFiniteAdeleEquiv T hAway).injective
  rw [LinearEquiv.apply_symm_apply]
  change _ = awayRationalEquiv T m
    (Tate.primeToFiniteAdeleAction (Gm S).toGrp T hAway a _)
  rw [awayRationalEquiv_primeToFiniteAdeleAction]
  exact congrArg (TateTwist.Divisibility.primeToFiniteAdeleAction Γ(T.left, ⊤) hAway a)
    ((primeToFiniteAdeleEquiv T hAway).apply_symm_apply x).symm

/-- The finite-adelic bundles retain the full-to-away restriction square. -/
theorem primeToFiniteAdeleEquiv_restrictAway (x : Tate.RationalFull (Gm S).toGrp T) :
    primeToFiniteAdeleEquiv T hAway (Tate.rationalRestrictAway (Gm S).toGrp T m x) =
      TateTwist.Divisibility.rationalRestrictAway Γ(T.left, ⊤) m
        (finiteAdeleEquiv T (fun _ => True) h x) :=
  awayRationalEquiv_restrictAway T m x

/-- The inverse finite-adelic bundles retain the same restriction square. -/
theorem primeToFiniteAdeleEquiv_symm_restrictAway
    (x : TateTwist.Divisibility.RationalFull Γ(T.left, ⊤)) :
    (primeToFiniteAdeleEquiv T hAway).symm
        (TateTwist.Divisibility.rationalRestrictAway Γ(T.left, ⊤) m x) =
      Tate.rationalRestrictAway (Gm S).toGrp T m
        ((finiteAdeleEquiv T (fun _ => True) h).symm x) :=
  awayRationalEquiv_symm_restrictAway T m x

end Langlands.GroupScheme.Gm.TateComparison
