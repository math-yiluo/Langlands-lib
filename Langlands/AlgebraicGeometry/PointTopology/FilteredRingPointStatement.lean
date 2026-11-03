import Langlands.AlgebraicGeometry.PointTopology.FilteredRingPoints
import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Filtered colimits of actual relative scheme points

The fixed-model comparison behind Conrad (3.5.1), with the weaker hypotheses
for equality descent retained separately from existence descent.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- Actual point-colimit injectivity and eventual equality under locally finite
 type, and factorization and bijectivity under locally finite presentation. -/
def FilteredRingPointComparison : Prop :=
  ∀ (R : Type u) [CommRing R] (J : Type u) [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{u} R) (c : Cocone F) (_hc : IsColimit c)
    (X : Over (Spec (CommRingCat.of R))),
    (LocallyOfFiniteType X.hom →
      Function.Injective (ringPointColimitMap R F X c) ∧
      (∀ (i j : J) (p : RingPoint R X (F.obj i)) (q : RingPoint R X (F.obj j)),
        p.changeRing (c.ι.app i).hom = q.changeRing (c.ι.app j).hom ↔
          ∃ (k : J) (f : i ⟶ k) (g : j ⟶ k),
            p.changeRing (F.map f).hom = q.changeRing (F.map g).hom) ∧
      (∀ (i : J) (p q : RingPoint R X (F.obj i)),
        p.changeRing (c.ι.app i).hom = q.changeRing (c.ι.app i).hom ↔
          ∃ (k : J) (f : i ⟶ k),
            p.changeRing (F.map f).hom = q.changeRing (F.map f).hom)) ∧
    (LocallyOfFinitePresentation X.hom →
      (∀ p : RingPoint R X c.pt,
        ∃ (i : J) (q : RingPoint R X (F.obj i)), q.changeRing (c.ι.app i).hom = p) ∧
      Function.Surjective (ringPointColimitMap R F X c) ∧
      Function.Bijective (ringPointColimitMap R F X c))

end Langlands.AlgebraicGeometry.PointTopology
