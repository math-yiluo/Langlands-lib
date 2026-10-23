import Langlands.AbelianScheme.Tate.IntegralBaseChange
import Langlands.AbelianScheme.Tate.RationalTestScheme

/-! # Base change of actual rational Tate modules -/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

universe u
namespace Langlands.GroupScheme.Tate

variable {S S' : Scheme.{u}} (b : S' ⟶ S)
  (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S')

/-- Scalar extension of the actual integral pullback comparison. -/
def rationalBaseChange (P : ℕ → Prop) :
    Rational ((Over.pullback b).mapGrp.obj G) T P ≃ₗ[ℚ]
      Rational G ((Over.map b).obj T) P :=
  (integralBaseChange b G T P).toIntLinearEquiv.baseChange ℤ ℚ _ _

@[simp] theorem rationalBaseChange_tmul (P : ℕ → Prop)
    (q : ℚ) (x : Integral ((Over.pullback b).mapGrp.obj G) T P) :
    rationalBaseChange b G T P (q ⊗ₜ[ℤ] x) =
      q ⊗ₜ[ℤ] integralBaseChange b G T P x := rfl

@[simp] theorem rationalBaseChange_symm_tmul (P : ℕ → Prop)
    (q : ℚ) (x : Integral G ((Over.map b).obj T) P) :
    (rationalBaseChange b G T P).symm (q ⊗ₜ[ℤ] x) =
      q ⊗ₜ[ℤ] (integralBaseChange b G T P).symm x := rfl

/-- Base change commutes with the integral-to-rational map. -/
@[simp] theorem rationalBaseChange_toRational (P : ℕ → Prop)
    (x : Integral ((Over.pullback b).mapGrp.obj G) T P) :
    rationalBaseChange b G T P (toRational _ T P x) =
      toRational G ((Over.map b).obj T) P (integralBaseChange b G T P x) := rfl

/-- Full-to-away restriction commutes with rational base change. -/
theorem rationalBaseChange_restrictAway (m : ℕ)
    (x : RationalFull ((Over.pullback b).mapGrp.obj G) T) :
    rationalBaseChange b G T (fun n => Nat.Coprime n m) (rationalRestrictAway _ T m x) =
      rationalRestrictAway G ((Over.map b).obj T) m
        (rationalBaseChange b G T (fun _ => True) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x => rfl
  | add x y hx hy => simp_all

/-- Rationalized full residue scalars commute with base change. -/
theorem rationalBaseChange_scalarAction (P : ℕ → Prop)
    (a : ℚ ⊗[ℤ] Global.ProfiniteIntegerRing)
    (x : Rational ((Over.pullback b).mapGrp.obj G) T P) :
    rationalBaseChange b G T P (rationalScalarAction _ T P a x) =
      rationalScalarAction G ((Over.map b).obj T) P a (rationalBaseChange b G T P x) :=
  TateScalarExtension.map_action
    (integralBaseChangeLinearEquiv b G T P).toLinearEquiv.toLinearMap a x

/-- The same full scalar comparison is used at both endpoints. -/
theorem rationalBaseChange_finiteAdeleAction (P : ℕ → Prop)
    (h : Global.RationalProfiniteIntegerAdeleComparison) (a : Global.FiniteAdeles ℚ)
    (x : Rational ((Over.pullback b).mapGrp.obj G) T P) :
    rationalBaseChange b G T P (finiteAdeleAction _ T P h a x) =
      finiteAdeleAction G ((Over.map b).obj T) P h a (rationalBaseChange b G T P x) :=
  rationalBaseChange_scalarAction b G T P _ x

/-- Base change over the existing finite-adelic scalar ring. -/
def finiteAdeleBaseChange (P : ℕ → Prop)
    (h : Global.RationalProfiniteIntegerAdeleComparison) :
    let := finiteAdeleModule ((Over.pullback b).mapGrp.obj G) T P h
    let := finiteAdeleModule G ((Over.map b).obj T) P h
    Rational ((Over.pullback b).mapGrp.obj G) T P ≃ₗ[Global.FiniteAdeles ℚ]
      Rational G ((Over.map b).obj T) P := by
  let := finiteAdeleModule ((Over.pullback b).mapGrp.obj G) T P h
  let := finiteAdeleModule G ((Over.map b).obj T) P h
  exact { (rationalBaseChange b G T P).toEquiv with
    map_add' := (rationalBaseChange b G T P).map_add
    map_smul' := rationalBaseChange_finiteAdeleAction b G T P h }

@[simp] theorem finiteAdeleBaseChange_apply (P : ℕ → Prop)
    (h : Global.RationalProfiniteIntegerAdeleComparison)
    (x : Rational ((Over.pullback b).mapGrp.obj G) T P) :
    finiteAdeleBaseChange b G T P h x = rationalBaseChange b G T P x := rfl

/-- Rationalized away residue scalars commute with base change. -/
theorem rationalBaseChange_awayScalarAction (m : ℕ)
    (a : ℚ ⊗[ℤ] Global.PrimeToProfiniteIntegerRing m)
    (x : RationalAway ((Over.pullback b).mapGrp.obj G) T m) :
    rationalBaseChange b G T (fun n => Nat.Coprime n m) (rationalAwayScalarAction _ T m a x) =
      rationalAwayScalarAction G ((Over.map b).obj T) m a
        (rationalBaseChange b G T (fun n => Nat.Coprime n m) x) :=
  TateScalarExtension.map_action
    (awayBaseChangeLinearEquiv b G T m).toLinearEquiv.toLinearMap a x

variable {h : Global.RationalProfiniteIntegerAdeleComparison} {m : ℕ}

/-- The same coupled away scalar comparison is used at both endpoints. -/
theorem rationalBaseChange_primeToFiniteAdeleAction
    (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
    (a : Global.PrimeToFiniteAdeles m)
    (x : RationalAway ((Over.pullback b).mapGrp.obj G) T m) :
    rationalBaseChange b G T (fun n => Nat.Coprime n m) (primeToFiniteAdeleAction _ T hAway a x) =
      primeToFiniteAdeleAction G ((Over.map b).obj T) hAway a
        (rationalBaseChange b G T (fun n => Nat.Coprime n m) x) :=
  rationalBaseChange_awayScalarAction b G T m _ x

/-- Base change over the existing prime-to-modulus finite-adeles. -/
def primeToFiniteAdeleBaseChange
    (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m) :
    let := primeToFiniteAdeleModule ((Over.pullback b).mapGrp.obj G) T hAway
    let := primeToFiniteAdeleModule G ((Over.map b).obj T) hAway
    RationalAway ((Over.pullback b).mapGrp.obj G) T m ≃ₗ[Global.PrimeToFiniteAdeles m]
      RationalAway G ((Over.map b).obj T) m := by
  let := primeToFiniteAdeleModule ((Over.pullback b).mapGrp.obj G) T hAway
  let := primeToFiniteAdeleModule G ((Over.map b).obj T) hAway
  exact { (rationalBaseChange b G T (fun n => Nat.Coprime n m)).toEquiv with
    map_add' := (rationalBaseChange b G T (fun n => Nat.Coprime n m)).map_add
    map_smul' := rationalBaseChange_primeToFiniteAdeleAction b G T hAway }

@[simp] theorem primeToFiniteAdeleBaseChange_apply
    (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
    (x : RationalAway ((Over.pullback b).mapGrp.obj G) T m) :
    primeToFiniteAdeleBaseChange b G T hAway x =
      rationalBaseChange b G T (fun n => Nat.Coprime n m) x := rfl

variable {T}

/-- Rational base change is natural under restriction of the test scheme. -/
theorem rationalBaseChange_testRestrict {T' : Over S'} (P : ℕ → Prop) (a : T' ⟶ T)
    (x : Rational ((Over.pullback b).mapGrp.obj G) T P) :
    rationalBaseChange b G T' P (rationalTestRestrict _ P a x) =
      rationalTestRestrict G P ((Over.map b).map a) (rationalBaseChange b G T P x) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x =>
    simp only [rationalTestRestrict_tmul, rationalBaseChange_tmul,
      integralBaseChange_testRestrict]
  | add x y hx hy => simp_all

variable (T) {G} {H : Grp (Over S)} [IsCommMonObj H.X]

/-- Rational base change is natural in actual group-scheme homomorphisms. -/
theorem rationalBaseChange_map (P : ℕ → Prop) (f : G ⟶ H)
    (x : Rational ((Over.pullback b).mapGrp.obj G) T P) :
    rationalBaseChange b H T P (rationalMap T P ((Over.pullback b).mapGrp.map f) x) =
      rationalMap ((Over.map b).obj T) P f (rationalBaseChange b G T P x) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x =>
    simp only [rationalMap_tmul, rationalBaseChange_tmul, integralBaseChange_map]
  | add x y hx hy => simp_all

end Langlands.GroupScheme.Tate

namespace Langlands.AbelianScheme.Tate

variable {S S' : Scheme.{u}} (b : S' ⟶ S) (A : AbelianScheme S) (T : Over S')

/-- Actual rational Tate base change for bundled abelian schemes. -/
abbrev rationalBaseChange (P : ℕ → Prop) :
    Rational ((AbelianScheme.baseChange b).obj A) T P ≃ₗ[ℚ]
      Rational A ((Over.map b).obj T) P :=
  GroupScheme.Tate.rationalBaseChange b A.toGrp T P

/-- The abelian-scheme comparison with the same full scalar witness. -/
abbrev finiteAdeleBaseChange (P : ℕ → Prop)
    (h : Global.RationalProfiniteIntegerAdeleComparison) :
    let := finiteAdeleModule ((AbelianScheme.baseChange b).obj A) T P h
    let := finiteAdeleModule A ((Over.map b).obj T) P h
    Rational ((AbelianScheme.baseChange b).obj A) T P ≃ₗ[Global.FiniteAdeles ℚ]
      Rational A ((Over.map b).obj T) P :=
  GroupScheme.Tate.finiteAdeleBaseChange b A.toGrp T P h

/-- The abelian-scheme comparison with the same coupled away scalar witnesses. -/
abbrev primeToFiniteAdeleBaseChange {h : Global.RationalProfiniteIntegerAdeleComparison}
    {m : ℕ} (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m) :
    let := primeToFiniteAdeleModule ((AbelianScheme.baseChange b).obj A) T hAway
    let := primeToFiniteAdeleModule A ((Over.map b).obj T) hAway
    RationalAway ((AbelianScheme.baseChange b).obj A) T m ≃ₗ[Global.PrimeToFiniteAdeles m]
      RationalAway A ((Over.map b).obj T) m :=
  GroupScheme.Tate.primeToFiniteAdeleBaseChange b A.toGrp T hAway

/-- Rational full base change at a field-valued point. -/
abbrev rationalFullBaseChangeAt {Ω : Type u} [Field Ω] (t : Spec (.of Ω) ⟶ S') :
    RationalFullAt ((AbelianScheme.baseChange b).obj A) t ≃ₗ[ℚ]
      RationalFullAt A (t ≫ b) :=
  rationalBaseChange b A (Over.mk t) (fun _ => True)

/-- Rational away base change at the same field-valued point. -/
abbrev rationalAwayBaseChangeAt {Ω : Type u} [Field Ω] (t : Spec (.of Ω) ⟶ S') (m : ℕ) :
    RationalAwayAt ((AbelianScheme.baseChange b).obj A) t m ≃ₗ[ℚ]
      RationalAwayAt A (t ≫ b) m :=
  rationalBaseChange b A (Over.mk t) (fun n => Nat.Coprime n m)

variable {A} {B : AbelianScheme S}

/-- The actual abelian-scheme homomorphism square after rationalization. -/
theorem rationalBaseChange_map (P : ℕ → Prop) (f : A ⟶ B)
    (x : Rational ((AbelianScheme.baseChange b).obj A) T P) :
    rationalBaseChange b B T P (rationalMap T P ((AbelianScheme.baseChange b).map f) x) =
      rationalMap ((Over.map b).obj T) P f (rationalBaseChange b A T P x) :=
  GroupScheme.Tate.rationalBaseChange_map b T P (AbelianScheme.groupHom f) x

end Langlands.AbelianScheme.Tate
