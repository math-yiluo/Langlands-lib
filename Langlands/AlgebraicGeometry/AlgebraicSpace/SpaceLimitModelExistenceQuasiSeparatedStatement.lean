import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceBaseChange
import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasGeometry

/-!
# Models of quasi-separated algebraic spaces along cofiltered limits of affine schemes

Conrad, printed p.13: Theorem 3.4 holds with finitely presented algebraic spaces in place of
finitely presented schemes. This file states the existence of models: a quasi-separated
algebraic space of finite presentation over the limit of a cofiltered diagram of affine
schemes is the base change of a quasi-separated algebraic space of finite presentation over
some stage.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Model existence for quasi-separated algebraic spaces along a cofiltered limit of affine
schemes. A quasi-separated space over the limit with a quasi-compact, locally finitely
presented atlas is isomorphic to the base change of a quasi-separated space over some stage
with such an atlas. -/
def SpaceLimitModelExistenceQuasiSeparated : Prop :=
  ∀ (I : Type u) [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)] (c : Cone D) (_hc : IsLimit c)
    (Y : AlgebraicSpace c.pt), IsQuasiSeparated Y →
    HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) Y →
      ∃ (i : I) (X : AlgebraicSpace (D.obj i)), IsQuasiSeparated X ∧
        HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X ∧
        Nonempty (baseChange (c.π.app i) X ≅ Y)

end Langlands.AlgebraicGeometry.AlgebraicSpace
