/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective


public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.ChowRelativeAmpleGeometric
import WeilConjectures.AlgebraicGeometry.ChowRelativeAmpleTwist

/-!
# Chow immersion and relative ampleness

Source: Stacks Project, Cohomology of Schemes, Remark 30.18.2 and
Proposition 30.19.1, Tag 02O5 (blueprint: lem-pc-chow-relative-ample).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry

set_option linter.unusedVariables false in
/-- The Chow immersion is closed and its pulled-back twisting module is relatively ample.
Source: Stacks Project, Cohomology of Schemes, Remark 30.18.2 and Proposition 30.19.1,
Tag 02O5 (blueprint: theorem-chow-s-lemma-projective-form--2).

Proof:
1. Compose the two proper morphisms (theorem-chow-s-lemma-projective-form--2). Projective
   space is proper and hence separated (lemma-nagata-projective-space-base-change-proper,
   theorem-chow-s-lemma-projective-form--2). Proper-over-separated makes `j` proper
   (theorem-chow-s-lemma-projective-form--2), so its image is closed. The immersion criterion
   makes `j` closed (theorem-chow-s-lemma-projective-form--2). Properness
   gives quasi-compactness, so the factorization makes `π ≫ g` projective
   (theorem-chow-s-lemma-projective-form--2).
2. Base change `j` along `g`. The graph of `π` is the base change of the closed
   diagonal of `g`, which is separated since it is proper. Thus the graph and the
   base-changed `j` are closed immersions. Their composite is `liftBaseChange π j hj`;
   permanence and the closed-image criterion make it closed. Properness of `π`
   supplies quasi-compactness, giving projectivity of `π`. Both twists are pulled
   from the same integral Proj twist, and the two composites to the integral model
   agree. Composition compatibility of tensor pullback gives their isomorphism
   (theorem-chow-s-lemma-projective-form--2, theorem-chow-s-lemma-projective-form--2,
   theorem-chow-s-lemma-projective-form--2, theorem-chow-s-lemma-projective-form--2,
   theorem-chow-s-lemma-projective-form--2, theorem-chow-s-lemma-projective-form--2).
3. For an affine open `V` of `S`, base change the closed immersion `j` to `V`.
   Pullback composition identifies its pulled-back O(1) with the restriction of `L`.
   The affine-base projective ampleness theorem proves invertibility and ampleness
   (theorem-chow-s-lemma-projective-form--2, theorem-chow-s-lemma-projective-form--2,
   theorem-chow-s-lemma-projective-form--2, theorem-chow-s-lemma-projective-form--2,
   theorem-chow-s-lemma-projective-form--2). Invertibility of `L` itself follows from
   the standard-chart trivializations of the integral twist and tensor pullback.
4. For an affine open `W` of `Z`, apply the same argument to the closed immersion
   `liftBaseChange π j hj`. The isomorphism in step 2 identifies its pulled-back O(1)
   with `L`, so the same affine-base theorem gives the second ampleness clause
   (the same five nodes as step 3).
-/
theorem chow_relative_ample (m : ℕ) (S Z X' : Scheme.{u})
    (g : Z ⟶ S) (π : X' ⟶ Z)
    (j : X' ⟶ ℙ(ULift.{u} (Fin (m + 1)); S))
    [IsProper g] [IsProper π] [IsImmersion j]
    (hj : π ≫ g = j ≫ (ℙ(ULift.{u} (Fin (m + 1)); S) ↘ S)) :
    IsClosedImmersion j ∧ IsProjective (π ≫ g) ∧
      IsClosedImmersion (ProjectiveSpace.liftBaseChange π j hj) ∧ IsProjective π ∧
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
  have hA := chow_relative_ample_geometric m S Z X' g π j hj
  have hB := chow_relative_ample_twist m S Z X' g π j hj
  exact ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2, hB⟩

end AlgebraicGeometry
