import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceBaseChange
import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasGeometry

/-!
# Models of algebraic spaces along cofiltered limits of affine schemes

Conrad, printed p.13: Theorem 3.4 holds with finitely presented algebraic spaces in place of
finitely presented schemes. This file states the existence of models: a separated algebraic
space of finite presentation over the limit of a cofiltered diagram of affine schemes is the
base change of a separated algebraic space of finite presentation over some stage.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Model existence for separated algebraic spaces along a cofiltered limit of affine schemes.
A separated space over the limit with a quasi-compact, locally finitely presented atlas is
isomorphic to the base change of a separated space over some stage with such an atlas. -/
def SpaceLimitModelExistence : Prop :=
  ∀ (I : Type u) [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)] (c : Cone D) (_hc : IsLimit c)
    (Y : AlgebraicSpace c.pt), IsSeparated Y →
    HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) Y →
      ∃ (i : I) (X : AlgebraicSpace (D.obj i)), IsSeparated X ∧
        HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X ∧
        Nonempty (baseChange (c.π.app i) X ≅ Y)

end Langlands.AlgebraicGeometry.AlgebraicSpace
