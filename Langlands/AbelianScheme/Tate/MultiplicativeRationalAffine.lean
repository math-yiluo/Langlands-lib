import Langlands.AbelianScheme.Tate.MultiplicativeDivisibilityAffine
import Langlands.AbelianScheme.Tate.MultiplicativeRational
import Langlands.AbelianScheme.Tate.TwistAwayRationalScalars

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.Gm.TateComparison
universe u
variable {S : Scheme.{u}} {R : CommRingCat.{u}} (f : Spec R ⟶ S) (P : ℕ → Prop)

/-- Extend scalars over the integers in the affine integral comparison. -/
def affineRationalEquiv :
    Tate.Rational (Gm S).toGrp (Over.mk f) P ≃ₗ[ℚ]
      TateTwist.Divisibility.Rational R P :=
  (affineIntegralEquiv f P).toAddEquiv.toIntLinearEquiv.baseChange ℤ ℚ _ _

@[simp] theorem affineRationalEquiv_tmul (q : ℚ)
    (x : Tate.Integral (Gm S).toGrp (Over.mk f) P) :
    affineRationalEquiv f P (q ⊗ₜ[ℤ] x) = q ⊗ₜ[ℤ] affineIntegralEquiv f P x := rfl

@[simp] theorem affineRationalEquiv_symm_tmul (q : ℚ)
    (x : TateTwist.Divisibility.Integral R P) :
    (affineRationalEquiv f P).symm (q ⊗ₜ[ℤ] x) =
      q ⊗ₜ[ℤ] (affineIntegralEquiv f P).symm x := rfl

@[simp] theorem affineRationalEquiv_toRational
    (x : Tate.Integral (Gm S).toGrp (Over.mk f) P) :
    affineRationalEquiv f P (Tate.toRational (Gm S).toGrp (Over.mk f) P x) =
      TateTwist.Divisibility.toRational R P (affineIntegralEquiv f P x) := rfl

/-- Rationalizing the affine map agrees with canonical transport of the rational twist. -/
theorem affineRationalEquiv_apply (x : Tate.Rational (Gm S).toGrp (Over.mk f) P) :
    affineRationalEquiv f P x =
      TateTwist.Divisibility.rationalMap P (Scheme.ΓSpecIso R).hom.hom
        (rationalEquiv (Over.mk f) P x) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x => rfl
  | add x y hx hy => simp_all

/-- The inverse uses the inverse canonical section map. -/
theorem affineRationalEquiv_symm_apply (x : TateTwist.Divisibility.Rational R P) :
    (affineRationalEquiv f P).symm x =
      (rationalEquiv (Over.mk f) P).symm
        (TateTwist.Divisibility.rationalMap P (Scheme.ΓSpecIso R).inv.hom x) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x => rfl
  | add x y hx hy => simp_all

theorem affineRationalEquiv_scalarAction (a : ℚ ⊗[ℤ] Global.ProfiniteIntegerRing)
    (x : Tate.Rational (Gm S).toGrp (Over.mk f) P) :
    affineRationalEquiv f P (Tate.rationalScalarAction (Gm S).toGrp (Over.mk f) P a x) =
      TateTwist.Divisibility.rationalScalarAction R P a (affineRationalEquiv f P x) :=
  TateScalarExtension.map_action (affineIntegralEquiv f P).toLinearMap a x

theorem affineRationalEquiv_finiteAdeleAction
    (h : Global.RationalProfiniteIntegerAdeleComparison) (a : Global.FiniteAdeles ℚ)
    (x : Tate.Rational (Gm S).toGrp (Over.mk f) P) :
    affineRationalEquiv f P (Tate.finiteAdeleAction (Gm S).toGrp (Over.mk f) P h a x) =
      TateTwist.Divisibility.finiteAdeleAction R P h a (affineRationalEquiv f P x) :=
  affineRationalEquiv_scalarAction f P _ x

/-- The affine selected comparison is linear over the full finite adeles. -/
def affineFiniteAdeleEquiv (h : Global.RationalProfiniteIntegerAdeleComparison) :
    let := Tate.finiteAdeleModule (Gm S).toGrp (Over.mk f) P h
    let := TateTwist.Divisibility.finiteAdeleModule R P h
    Tate.Rational (Gm S).toGrp (Over.mk f) P ≃ₗ[Global.FiniteAdeles ℚ]
      TateTwist.Divisibility.Rational R P := by
  let := Tate.finiteAdeleModule (Gm S).toGrp (Over.mk f) P h
  let := TateTwist.Divisibility.finiteAdeleModule R P h
  exact { (affineRationalEquiv f P).toAddEquiv with
    map_smul' := affineRationalEquiv_finiteAdeleAction f P h }

@[simp] theorem affineFiniteAdeleEquiv_apply
    (h : Global.RationalProfiniteIntegerAdeleComparison)
    (x : Tate.Rational (Gm S).toGrp (Over.mk f) P) :
    affineFiniteAdeleEquiv f P h x = affineRationalEquiv f P x := rfl

/-- Rational affine comparison at every positive order. -/
abbrev affineFullRationalEquiv :
    Tate.RationalFull (Gm S).toGrp (Over.mk f) ≃ₗ[ℚ]
      TateTwist.Divisibility.RationalFull R :=
  affineRationalEquiv f (fun _ => True)

variable (m : ℕ)

/-- Rational affine comparison at orders coprime to the modulus. -/
abbrev affineAwayRationalEquiv :
    Tate.RationalAway (Gm S).toGrp (Over.mk f) m ≃ₗ[ℚ]
      TateTwist.Divisibility.RationalAway R m :=
  affineRationalEquiv f (fun n => Nat.Coprime n m)

theorem affineAwayRationalEquiv_scalarAction
    (a : ℚ ⊗[ℤ] Global.PrimeToProfiniteIntegerRing m)
    (x : Tate.RationalAway (Gm S).toGrp (Over.mk f) m) :
    affineAwayRationalEquiv f m
        (Tate.rationalAwayScalarAction (Gm S).toGrp (Over.mk f) m a x) =
      TateTwist.Divisibility.rationalAwayScalarAction R m a (affineAwayRationalEquiv f m x) :=
  TateScalarExtension.map_action (affineAwayEquiv f m).toLinearMap a x

variable {m} {h : Global.RationalProfiniteIntegerAdeleComparison}
variable (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)

theorem affineAwayRationalEquiv_primeToFiniteAdeleAction (a : Global.PrimeToFiniteAdeles m)
    (x : Tate.RationalAway (Gm S).toGrp (Over.mk f) m) :
    affineAwayRationalEquiv f m
        (Tate.primeToFiniteAdeleAction (Gm S).toGrp (Over.mk f) hAway a x) =
      TateTwist.Divisibility.primeToFiniteAdeleAction R hAway a
        (affineAwayRationalEquiv f m x) :=
  affineAwayRationalEquiv_scalarAction f m _ x

/-- The affine away comparison uses the coupled away scalar comparison. -/
def affinePrimeToFiniteAdeleEquiv :
    let := Tate.primeToFiniteAdeleModule (Gm S).toGrp (Over.mk f) hAway
    let := TateTwist.Divisibility.primeToFiniteAdeleModule R hAway
    Tate.RationalAway (Gm S).toGrp (Over.mk f) m ≃ₗ[Global.PrimeToFiniteAdeles m]
      TateTwist.Divisibility.RationalAway R m := by
  let := Tate.primeToFiniteAdeleModule (Gm S).toGrp (Over.mk f) hAway
  let := TateTwist.Divisibility.primeToFiniteAdeleModule R hAway
  exact { (affineAwayRationalEquiv f m).toAddEquiv with
    map_smul' := affineAwayRationalEquiv_primeToFiniteAdeleAction f hAway }

@[simp] theorem affinePrimeToFiniteAdeleEquiv_apply
    (x : Tate.RationalAway (Gm S).toGrp (Over.mk f) m) :
    affinePrimeToFiniteAdeleEquiv f hAway x = affineAwayRationalEquiv f m x := rfl

variable (m)

/-- Affine rationalization commutes with full-to-away restriction. -/
theorem affineAwayRationalEquiv_restrictAway
    (x : Tate.RationalFull (Gm S).toGrp (Over.mk f)) :
    affineAwayRationalEquiv f m (Tate.rationalRestrictAway (Gm S).toGrp (Over.mk f) m x) =
      TateTwist.Divisibility.rationalRestrictAway R m (affineFullRationalEquiv f x) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x => rfl
  | add x y hx hy => simp_all

/-- The inverse affine rationalization commutes with the same restriction. -/
theorem affineAwayRationalEquiv_symm_restrictAway
    (x : TateTwist.Divisibility.RationalFull R) :
    (affineAwayRationalEquiv f m).symm (TateTwist.Divisibility.rationalRestrictAway R m x) =
      Tate.rationalRestrictAway (Gm S).toGrp (Over.mk f) m
        ((affineFullRationalEquiv f).symm x) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x => rfl
  | add x y hx hy => simp_all

variable {m}

/-- The full and away finite-adelic bundles retain that restriction square. -/
theorem affinePrimeToFiniteAdeleEquiv_restrictAway
    (x : Tate.RationalFull (Gm S).toGrp (Over.mk f)) :
    affinePrimeToFiniteAdeleEquiv f hAway
        (Tate.rationalRestrictAway (Gm S).toGrp (Over.mk f) m x) =
      TateTwist.Divisibility.rationalRestrictAway R m
        (affineFiniteAdeleEquiv f (fun _ => True) h x) :=
  affineAwayRationalEquiv_restrictAway f m x

/-- The inverse finite-adelic bundles retain the inverse restriction square. -/
theorem affinePrimeToFiniteAdeleEquiv_symm_restrictAway
    (x : TateTwist.Divisibility.RationalFull R) :
    (affinePrimeToFiniteAdeleEquiv f hAway).symm
        (TateTwist.Divisibility.rationalRestrictAway R m x) =
      Tate.rationalRestrictAway (Gm S).toGrp (Over.mk f) m
        ((affineFiniteAdeleEquiv f (fun _ => True) h).symm x) :=
  affineAwayRationalEquiv_symm_restrictAway f m x

end Langlands.GroupScheme.Gm.TateComparison
