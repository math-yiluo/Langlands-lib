/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.AlgebraicGeometry.TensorPullback


/-! Auxiliary decomposition for Chow relative ampleness. -/

@[expose] public section
universe u
open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
namespace AlgebraicGeometry
/-- Auxiliary component of the Chow relative ampleness theorem.
Source: Stacks Project, Cohomology of Schemes, Proposition 30.19.1 (Tag 02O5).
Proof in words: this strict component is obtained by the tensor-pullback
functoriality (for the isomorphism component) or by the affine-local standard
chart argument (for the properties component), exactly as in the parent proof.
(blueprint: lem-pc-chow-relative-ample-twist-iso) -/
theorem chow_relative_ample_twist_iso (m : ℕ) (S Z X' : Scheme.{u})
    (g : Z ⟶ S) (π : X' ⟶ Z)
    (j : X' ⟶ ℙ(ULift.{u} (Fin (m + 1)); S))
    [IsProper g] [IsProper π] [IsImmersion j]
    (hj : π ≫ g = j ≫ (ℙ(ULift.{u} (Fin (m + 1)); S) ↘ S)) :
      Nonempty (((Scheme.Modules.tensorPullback j).obj
          ((Scheme.Modules.tensorPullback (ProjectiveSpace.toProjInt
            (ULift.{u} (Fin (m + 1))) S)).obj
            (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (m + 1)))
              (ULift.{u} ℤ)) 1))) ≅
        ((Scheme.Modules.tensorPullback (ProjectiveSpace.liftBaseChange π j hj)).obj
            ((Scheme.Modules.tensorPullback (ProjectiveSpace.toProjInt
              (ULift.{u} (Fin (m + 1))) Z)).obj
              (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (m + 1)))
                (ULift.{u} ℤ)) 1)))) := by
  obtain ⟨eS⟩ := Scheme.Modules.nonempty_tensorPullbackComp j
    (ProjectiveSpace.toProjInt (ULift.{u} (Fin (m + 1))) S)
  obtain ⟨eZ⟩ := Scheme.Modules.nonempty_tensorPullbackComp
    (ProjectiveSpace.liftBaseChange π j hj)
    (ProjectiveSpace.toProjInt (ULift.{u} (Fin (m + 1))) Z)
  let L := Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (m + 1)))
    (ULift.{u} ℤ)) 1
  exact ⟨(eS.app L).symm ≪≫
    eqToIso (congrArg (fun f ↦ (Scheme.Modules.tensorPullback f).obj L)
      (ProjectiveSpace.liftBaseChange_toProjInt π j hj).symm) ≪≫ eZ.app L⟩

end AlgebraicGeometry
