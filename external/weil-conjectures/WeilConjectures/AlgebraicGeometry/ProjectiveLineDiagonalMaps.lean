/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedCartierKummer
/-!
Source: blueprint thm-amb-p1-adjunction.proof.md.
(auxiliary; not a blueprint node).

# Lower-level canonical diagonal projection maps -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale
/-- Either projection of the chosen fibre square of the projective line.
Source: blueprint lemma-class-diagonal-projective-line, first sentence
(blueprint: lemma-class-diagonal-projective-line). -/
def projectiveLineDiagonalProjection (S : Scheme.{u}) (a : Bool) :
    pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S) ⟶ ProjectiveLine S :=
  match a with
  | false => pullback.fst _ _
  | true => pullback.snd _ _

/-- The canonical projective-line chart for either projection, including its equation
over the base. It comes from projective-space base change and the flipped square.
Source: blueprint lemma-class-diagonal-projective-line, proof step 1
(blueprint: lemma-class-diagonal-projective-line). -/
def projectiveLineDiagonalChart (S : Scheme.{u}) (a : Bool) :
    {e : ProjectiveLine (ProjectiveLine S) ≅
      pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S) //
      e.hom ≫ projectiveLineDiagonalProjection S a =
        (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)} :=
  match a with
  | false => ⟨(ProjectiveSpace.isPullback_map (ULift (Fin 2))
      (ProjectiveLine S ↘ S)).flip.isoPullback,
      (ProjectiveSpace.isPullback_map (ULift (Fin 2))
        (ProjectiveLine S ↘ S)).flip.isoPullback_hom_fst⟩
  | true => ⟨(ProjectiveSpace.isPullback_map (ULift (Fin 2))
      (ProjectiveLine S ↘ S)).isoPullback,
      (ProjectiveSpace.isPullback_map (ULift (Fin 2))
        (ProjectiveLine S ↘ S)).isoPullback_hom_snd⟩

section
-- Reuse the coefficient structures used by the supported-class construction.
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

set_option linter.auxLemma false in
attribute [local instance 100000] ordinaryFiniteClass._proof_1 ordinaryFiniteClass._proof_2
  ordinaryFiniteClass._proof_3

/-- The canonical source identification A_P → Rp_* RDelta_* A_P. The two units
compose to the identity-map unit because p Delta = id, so this is the canonical
derived-composition identification, in the direction required by the integral.
Source: blueprint lemma-class-diagonal-projective-line, alpha_a and proof steps 3 and 5
(blueprint: lemma-class-diagonal-projective-line). -/
def projectiveLineDiagonalAlpha (A : Type (u + 1)) [CommRing A]
    (S : Scheme.{u}) (a : Bool) :
    ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).obj
        ((ordinaryFinitePushforward A (pullback.diagonal (ProjectiveLine S ↘ S))).obj
          (ordinaryFiniteUnit A (ProjectiveLine S))) :=
  constantSingleSectionUnits (ModuleCat.{u + 1} A)
    (pullback.diagonal (ProjectiveLine S ↘ S)) (projectiveLineDiagonalProjection S a)
    (𝟙_ (ModuleCat.{u + 1} A))

end

end AlgebraicGeometry.Etale
