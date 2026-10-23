import Langlands.AbelianScheme.Tate.MultiplicativeIntegralBaseChange
import Langlands.AbelianScheme.Tate.MultiplicativeRationalAffine
import Langlands.AbelianScheme.Tate.RationalBaseChange

noncomputable section
set_option maxHeartbeats 800000
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.Gm.TateComparison

universe u
variable {S S' : Scheme.{u}} (b : S' ⟶ S) (T : Over S')

/-- Rationalization over the integers of the actual multiplicative comparison. -/
def rationalBaseChange (P : ℕ → Prop) :
    Tate.Rational (Gm S').toGrp T P ≃ₗ[ℚ]
      Tate.Rational (Gm S).toGrp ((Over.map b).obj T) P :=
  (integralBaseChange b T P).toLinearEquiv.toAddEquiv.toIntLinearEquiv.baseChange ℤ ℚ _ _

@[simp] theorem rationalBaseChange_tmul (P : ℕ → Prop) (q : ℚ)
    (x : Tate.Integral (Gm S').toGrp T P) :
    rationalBaseChange b T P (q ⊗ₜ[ℤ] x) = q ⊗ₜ[ℤ] integralBaseChange b T P x := rfl

@[simp] theorem rationalBaseChange_toRational (P : ℕ → Prop)
    (x : Tate.Integral (Gm S').toGrp T P) :
    rationalBaseChange b T P (Tate.toRational (Gm S').toGrp T P x) =
      Tate.toRational (Gm S).toGrp ((Over.map b).obj T) P
        (integralBaseChange b T P x) := rfl

/-- Rationalization preserves the canonical root coordinate comparison. -/
theorem rationalEquiv_rationalBaseChange (P : ℕ → Prop)
    (x : Tate.Rational (Gm S').toGrp T P) :
    rationalEquiv ((Over.map b).obj T) P (rationalBaseChange b T P x) =
      rationalEquiv T P x := by
  induction x using TensorProduct.inductionOn with
  | tmul q x => simp only [rationalBaseChange_tmul, rationalEquiv_tmul,
      integralEquiv_integralBaseChange]
  | add x y hx hy => simp_all

/-- The rational comparison is actual pullback after the canonical Gm isomorphism. -/
theorem rationalBaseChange_eq_actual (P : ℕ → Prop)
    (x : Tate.Rational (Gm S').toGrp T P) :
    rationalBaseChange b T P x =
      Tate.rationalBaseChange b (Gm S).toGrp T P
        (Tate.rationalMap T P (Gm.baseChangeIso b).inv x) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x => simp only [rationalBaseChange_tmul, Tate.rationalMap_tmul,
      Tate.rationalBaseChange_tmul, integralBaseChange_eq_actual]
  | add x y hx hy => simp_all

/-- Rational base change preserves restriction to the coprime torsion orders. -/
theorem rationalBaseChange_restrictAway (m : ℕ)
    (x : Tate.RationalFull (Gm S').toGrp T) :
    rationalBaseChange b T (fun n => Nat.Coprime n m)
        (Tate.rationalRestrictAway (Gm S').toGrp T m x) =
      Tate.rationalRestrictAway (Gm S).toGrp ((Over.map b).obj T) m
        (rationalBaseChange b T (fun _ => True) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x => rfl
  | add x y hx hy => simp_all

/-- Compatibility with the scalar extension of the full residue action. -/
theorem rationalBaseChange_scalarAction (P : ℕ → Prop)
    (a : ℚ ⊗[ℤ] Global.ProfiniteIntegerRing) (x : Tate.Rational (Gm S').toGrp T P) :
    rationalBaseChange b T P (Tate.rationalScalarAction (Gm S').toGrp T P a x) =
      Tate.rationalScalarAction (Gm S).toGrp ((Over.map b).obj T) P a
        (rationalBaseChange b T P x) :=
  TateScalarExtension.map_action (integralBaseChange b T P).toLinearEquiv.toLinearMap a x

/-- Both finite-adelic actions use the same explicit scalar comparison. -/
theorem rationalBaseChange_finiteAdeleAction (P : ℕ → Prop)
    (h : Global.RationalProfiniteIntegerAdeleComparison) (a : Global.FiniteAdeles ℚ)
    (x : Tate.Rational (Gm S').toGrp T P) :
    rationalBaseChange b T P (Tate.finiteAdeleAction (Gm S').toGrp T P h a x) =
      Tate.finiteAdeleAction (Gm S).toGrp ((Over.map b).obj T) P h a
        (rationalBaseChange b T P x) :=
  rationalBaseChange_scalarAction b T P _ x

/-- The selected multiplicative comparison bundled over the finite adeles. -/
def finiteAdeleBaseChange (P : ℕ → Prop) (h : Global.RationalProfiniteIntegerAdeleComparison) :
    let := Tate.finiteAdeleModule (Gm S').toGrp T P h
    let := Tate.finiteAdeleModule (Gm S).toGrp ((Over.map b).obj T) P h
    Tate.Rational (Gm S').toGrp T P ≃ₗ[Global.FiniteAdeles ℚ]
      Tate.Rational (Gm S).toGrp ((Over.map b).obj T) P := by
  let := Tate.finiteAdeleModule (Gm S').toGrp T P h
  let := Tate.finiteAdeleModule (Gm S).toGrp ((Over.map b).obj T) P h
  exact { (rationalBaseChange b T P).toAddEquiv with
    map_smul' := rationalBaseChange_finiteAdeleAction b T P h }

@[simp] theorem finiteAdeleBaseChange_apply (P : ℕ → Prop)
    (h : Global.RationalProfiniteIntegerAdeleComparison) (x : Tate.Rational (Gm S').toGrp T P) :
    finiteAdeleBaseChange b T P h x = rationalBaseChange b T P x := rfl

/-- Compatibility with scalar extension of the away residue action. -/
theorem rationalBaseChange_awayScalarAction (m : ℕ)
    (a : ℚ ⊗[ℤ] Global.PrimeToProfiniteIntegerRing m)
    (x : Tate.RationalAway (Gm S').toGrp T m) :
    rationalBaseChange b T (fun n => Nat.Coprime n m)
        (Tate.rationalAwayScalarAction (Gm S').toGrp T m a x) =
      Tate.rationalAwayScalarAction (Gm S).toGrp ((Over.map b).obj T) m a
        (rationalBaseChange b T (fun n => Nat.Coprime n m) x) :=
  TateScalarExtension.map_action (awayBaseChange b T m).toLinearEquiv.toLinearMap a x

variable {h : Global.RationalProfiniteIntegerAdeleComparison} {m : ℕ}

/-- Both away finite-adelic actions use the same coupled scalar witnesses. -/
theorem rationalBaseChange_primeToFiniteAdeleAction
    (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
    (a : Global.PrimeToFiniteAdeles m) (x : Tate.RationalAway (Gm S').toGrp T m) :
    rationalBaseChange b T (fun n => Nat.Coprime n m)
        (Tate.primeToFiniteAdeleAction (Gm S').toGrp T hAway a x) =
      Tate.primeToFiniteAdeleAction (Gm S).toGrp ((Over.map b).obj T) hAway a
        (rationalBaseChange b T (fun n => Nat.Coprime n m) x) :=
  rationalBaseChange_awayScalarAction b T m _ x

/-- The away comparison bundled over the existing away finite-adeles. -/
def primeToFiniteAdeleBaseChange
    (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m) :
    let := Tate.primeToFiniteAdeleModule (Gm S').toGrp T hAway
    let := Tate.primeToFiniteAdeleModule (Gm S).toGrp ((Over.map b).obj T) hAway
    Tate.RationalAway (Gm S').toGrp T m ≃ₗ[Global.PrimeToFiniteAdeles m]
      Tate.RationalAway (Gm S).toGrp ((Over.map b).obj T) m := by
  let := Tate.primeToFiniteAdeleModule (Gm S').toGrp T hAway
  let := Tate.primeToFiniteAdeleModule (Gm S).toGrp ((Over.map b).obj T) hAway
  exact { (rationalBaseChange b T (fun n => Nat.Coprime n m)).toAddEquiv with
    map_smul' := rationalBaseChange_primeToFiniteAdeleAction b T hAway }

@[simp] theorem primeToFiniteAdeleBaseChange_apply
    (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
    (x : Tate.RationalAway (Gm S').toGrp T m) :
    primeToFiniteAdeleBaseChange b T hAway x =
      rationalBaseChange b T (fun n => Nat.Coprime n m) x := rfl

variable {T}

/-- Rational base change commutes with actual test-scheme restriction. -/
theorem rationalBaseChange_testRestrict {T' : Over S'} (P : ℕ → Prop) (a : T' ⟶ T)
    (x : Tate.Rational (Gm S').toGrp T P) :
    rationalBaseChange b T' P (Tate.rationalTestRestrict (Gm S').toGrp P a x) =
      Tate.rationalTestRestrict (Gm S).toGrp P ((Over.map b).map a)
        (rationalBaseChange b T P x) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x => simp only [Tate.rationalTestRestrict_tmul, rationalBaseChange_tmul,
      integralBaseChange_testRestrict]
  | add x y hx hy => simp_all

variable {R : CommRingCat.{u}} (t : Spec R ⟶ S')

/-- Rational affine root coordinates are unchanged by composing the point with the base map. -/
theorem affineRationalEquiv_rationalBaseChange (P : ℕ → Prop)
    (x : Tate.Rational (Gm S').toGrp (Over.mk t) P) :
    affineRationalEquiv (t ≫ b) P (rationalBaseChange b (Over.mk t) P x) =
      affineRationalEquiv t P x := by
  induction x using TensorProduct.inductionOn with
  | tmul q x =>
    change q ⊗ₜ[ℤ] affineIntegralEquiv (t ≫ b) P
      (integralBaseChange b (Over.mk t) P x) = q ⊗ₜ[ℤ] affineIntegralEquiv t P x
    rw [affineIntegralEquiv_integralBaseChange]
  | add x y hx hy => simp_all

end Langlands.GroupScheme.Gm.TateComparison
