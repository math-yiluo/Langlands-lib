import Langlands.AlgebraicGeometry.AlgebraicSpace.RingPoints
import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasGeometry
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Filtered colimits of ring-valued points of algebraic spaces

Conrad, printed p.13 and p.17: Theorem 3.4 holds with finitely presented algebraic
spaces in place of finitely presented schemes; in particular the points of such a space
over a filtered colimit of rings are the colimit of its points over the stages.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Points of an algebraic space over `Spec R` along a filtered colimit of `R`-algebras:
under a locally finite type atlas, two stage points agree over the colimit exactly when
they agree at a common later stage; under a locally finitely presented atlas, every
point over the colimit comes from a stage. -/
def SpaceFilteredRingPointComparison : Prop :=
  ∀ (R : Type u) [CommRing R] (J : Type u) [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{u} R) (c : Cocone F) (_hc : IsColimit c)
    (X : AlgebraicSpace (Spec (CommRingCat.of R))),
    (LocallyOfFiniteTypeOverBase X →
      ∀ (i j : J) (p : RingPoints R X (F.obj i)) (q : RingPoints R X (F.obj j)),
        RingPoints.changeRing (c.ι.app i).hom p = RingPoints.changeRing (c.ι.app j).hom q ↔
          ∃ (k : J) (f : i ⟶ k) (g : j ⟶ k),
            RingPoints.changeRing (F.map f).hom p = RingPoints.changeRing (F.map g).hom q) ∧
    (LocallyOfFinitePresentationOverBase X →
      ∀ p : RingPoints R X c.pt,
        ∃ (i : J) (q : RingPoints R X (F.obj i)),
          RingPoints.changeRing (c.ι.app i).hom q = p)

end Langlands.AlgebraicGeometry.AlgebraicSpace
