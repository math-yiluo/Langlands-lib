import Langlands.AlgebraicGeometry.PointTopology.Affine
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Topology.Algebra.Ring.Basic

/-! # Relative polynomial point spaces -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v w z

open Topology

namespace Langlands.AlgebraicGeometry.PointTopology.AlgPoint

variable {R : Type u} {A : Type v} {S : Type w}
variable [CommRing R] [CommRing A] [CommRing S] [Algebra R A] [Algebra R S]

/-- Evaluate a relative polynomial using a coefficient point and variable values. -/
def relativePolynomialPointLift (ι : Type z) (p : AlgPoint R A S) (x : ι → S) :
    AlgPoint R (MvPolynomial ι A) S :=
  ofAlgHom
    { MvPolynomial.eval₂Hom p.toAlgHom.toRingHom x with
      commutes' := fun r => by
        change MvPolynomial.eval₂Hom p.toAlgHom.toRingHom x
          (algebraMap R (MvPolynomial ι A) r) = algebraMap R S r
        rw [MvPolynomial.algebraMap_apply, MvPolynomial.eval₂Hom_C]
        exact p.toAlgHom.commutes r }

@[simp] theorem relativePolynomialPointLift_C (ι : Type z)
    (p : AlgPoint R A S) (x : ι → S) (a : A) :
    relativePolynomialPointLift ι p x (MvPolynomial.C a) = p a :=
  MvPolynomial.eval₂Hom_C _ _ _

@[simp] theorem relativePolynomialPointLift_X (ι : Type z)
    (p : AlgPoint R A S) (x : ι → S) (i : ι) :
    relativePolynomialPointLift ι p x (MvPolynomial.X i) = x i :=
  MvPolynomial.eval₂Hom_X' _ _ _

variable [TopologicalSpace S] [IsTopologicalRing S]

/-- Actual points of a relative polynomial algebra are coefficient points and
variable values, with the product topology. -/
def relativePolynomialPointHomeomorph (ι : Type z) :
    AlgPoint R (MvPolynomial ι A) S ≃ₜ (AlgPoint R A S × (ι → S)) where
  toFun p :=
    (precomp (IsScalarTower.toAlgHom R A (MvPolynomial ι A)) p,
      fun i => p (MvPolynomial.X i))
  invFun z := relativePolynomialPointLift ι z.1 z.2
  left_inv p := by
    ext P
    change MvPolynomial.eval₂Hom
      (precomp (IsScalarTower.toAlgHom R A (MvPolynomial ι A)) p).toAlgHom.toRingHom
      (fun i => p (MvPolynomial.X i)) P = p.toAlgHom P
    induction P using MvPolynomial.induction_on with
    | C a =>
        rw [MvPolynomial.eval₂Hom_C]
        rfl
    | add P Q hP hQ =>
        simpa only [map_add] using congrArg₂ (fun x y : S => x + y) hP hQ
    | mul_X P i hP =>
        simpa only [map_mul, MvPolynomial.eval₂Hom_X', toAlgHom_apply] using
          congrArg (fun x : S => x * p (MvPolynomial.X i)) hP
  right_inv z := by
    apply Prod.ext
    · ext a
      exact relativePolynomialPointLift_C ι z.1 z.2 a
    · funext i
      exact relativePolynomialPointLift_X ι z.1 z.2 i
  continuous_toFun :=
    (continuous_precomp _).prodMk (continuous_pi (fun _ => continuous_eval _))
  continuous_invFun := by
    apply (continuous_iff _).mpr
    intro P
    change Continuous (fun z : AlgPoint R A S × (ι → S) =>
      MvPolynomial.eval₂Hom z.1.toAlgHom.toRingHom z.2 P)
    induction P using MvPolynomial.induction_on with
    | C a =>
        simp only [MvPolynomial.eval₂Hom_C]
        convert (continuous_eval a).comp
          (continuous_fst : Continuous (Prod.fst : AlgPoint R A S × (ι → S) → _)) using 1
        rfl
    | add P Q hP hQ =>
        simpa only [map_add] using hP.fun_add hQ
    | mul_X P i hP =>
        simp only [map_mul, MvPolynomial.eval₂Hom_X']
        convert hP.fun_mul ((continuous_apply i).comp continuous_snd) using 1
        rfl

@[simp] theorem relativePolynomialPointHomeomorph_fst (ι : Type z)
    (p : AlgPoint R (MvPolynomial ι A) S) :
    (relativePolynomialPointHomeomorph (R := R) (A := A) (S := S) ι p).1 =
      precomp (IsScalarTower.toAlgHom R A (MvPolynomial ι A)) p := rfl

/-- Relative affine-space projection is open on actual algebra-map points. -/
theorem isOpenMap_precomp_mvPolynomial (ι : Type z) :
    IsOpenMap (precomp (S := S) (IsScalarTower.toAlgHom R A (MvPolynomial ι A))) :=
  isOpenMap_fst.comp (relativePolynomialPointHomeomorph (R := R) (A := A) ι).isOpenMap

end Langlands.AlgebraicGeometry.PointTopology.AlgPoint
