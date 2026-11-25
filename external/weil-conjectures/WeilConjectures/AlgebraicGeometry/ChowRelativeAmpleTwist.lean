/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.ChowRelativeAmpleTwistIso
import WeilConjectures.AlgebraicGeometry.ChowRelativeAmpleTwistProperties

@[expose] public section
universe u
open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
namespace AlgebraicGeometry

set_option linter.unusedVariables false in
/-- Twisting and ampleness consequences.

Source: Stacks Project, Cohomology of Schemes, Proposition 30.19.1 (Tag 02O5).
Proof in words: first apply `chow_relative_ample_geometric` to obtain both
closed immersions. Identify both displayed modules by functoriality of tensor
pullback, since the two composites to the integral projective model agree
under `hj`; this gives the displayed `Nonempty` isomorphism.  The standard
chart trivializations of the integral Proj twist pull back along `j`, proving
invertibility of the resulting module.  After restricting to an affine open
of `S` (respectively `Z`), base-change the closed immersion and apply the
affine-base theorem `projective_closedImmersion_ample_invertible` to obtain
invertibility and ampleness of the restriction. More explicitly, identify the
affine open with the spectrum of its section ring, transport the base-changed
immersion to that spectrum, and identify its twist with the restriction using
`ProjectiveSpace.liftBaseChange_toProjInt` and composite tensor pullback.
The standard-chart trivializations give invertibility before restriction; their
restrictions also give the witnesses `hV` and `hW`. The proof of ampleness is
independent of these witnesses by proof irrelevance. Transporting these properties
across the pullback
isomorphism gives both quantified affine-open clauses.

(blueprint: lem-pc-chow-relative-ample-twist) -/
theorem chow_relative_ample_twist (m : ℕ) (S Z X' : Scheme.{u})
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
                (ULift.{u} ℤ)) 1)))) ∧
      ∃ hL : ((Scheme.Modules.tensorPullback j).obj
          ((Scheme.Modules.tensorPullback (ProjectiveSpace.toProjInt
            (ULift.{u} (Fin (m + 1))) S)).obj
            (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (m + 1)))
              (ULift.{u} ℤ)) 1))).IsInvertible,
        (∀ V : S.Opens, IsAffineOpen V →
          ∃ hV : ((Scheme.Modules.tensorPullback ((π ≫ g) ⁻¹ᵁ V).ι).obj
              ((Scheme.Modules.tensorPullback j).obj
              ((Scheme.Modules.tensorPullback (ProjectiveSpace.toProjInt
                (ULift.{u} (Fin (m + 1))) S)).obj
                (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (m + 1)))
                  (ULift.{u} ℤ)) 1)))).IsInvertible,
            @Scheme.Modules.IsAmple ((π ≫ g) ⁻¹ᵁ V).toScheme
              ((Scheme.Modules.tensorPullback ((π ≫ g) ⁻¹ᵁ V).ι).obj
                  ((Scheme.Modules.tensorPullback j).obj
                  ((Scheme.Modules.tensorPullback (ProjectiveSpace.toProjInt
                    (ULift.{u} (Fin (m + 1))) S)).obj
                    (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (m + 1)))
                      (ULift.{u} ℤ)) 1)))) hV) ∧
        (∀ W : Z.Opens, IsAffineOpen W →
          ∃ hW : ((Scheme.Modules.tensorPullback (π ⁻¹ᵁ W).ι).obj
              ((Scheme.Modules.tensorPullback j).obj
              ((Scheme.Modules.tensorPullback (ProjectiveSpace.toProjInt
                (ULift.{u} (Fin (m + 1))) S)).obj
                (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (m + 1)))
                  (ULift.{u} ℤ)) 1)))).IsInvertible,
            @Scheme.Modules.IsAmple (π ⁻¹ᵁ W).toScheme
              ((Scheme.Modules.tensorPullback (π ⁻¹ᵁ W).ι).obj
                  ((Scheme.Modules.tensorPullback j).obj
                  ((Scheme.Modules.tensorPullback (ProjectiveSpace.toProjInt
                    (ULift.{u} (Fin (m + 1))) S)).obj
                    (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (m + 1)))
                      (ULift.{u} ℤ)) 1)))) hW) := by
  exact ⟨chow_relative_ample_twist_iso m S Z X' g π j hj,
    chow_relative_ample_twist_properties m S Z X' g π j hj⟩

end AlgebraicGeometry
