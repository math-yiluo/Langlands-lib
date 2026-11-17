import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # Potential geometric reducedness of the reduced generic fibre -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

namespace DvrPotentialGenericReduction

/-- The canonical reduced closed subscheme, with its given structural map. -/
def reducedOver {S : Scheme.{u}} (X : Over S) : Over S :=
  Over.mk ((Scheme.IdealSheafData.vanishingIdeal
    (⊤ : TopologicalSpace.Closeds X.left)).subschemeι ≫ X.hom)

end DvrPotentialGenericReduction

/-- After a faithfully flat DVR extension, the reduction of the actual generic
fibre of a flat finite-type scheme is geometrically reduced. -/
def DvrPotentialGenericReductionStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (X : Over (Spec (CommRingCat.of R))),
    Flat X.hom → LocallyOfFiniteType X.hom → QuasiCompact X.hom →
    ∃ (R' : Type u) (cR' : CommRing R'),
      letI := cR'
      ∃ (dR' : IsDomain R'),
        letI := dR'
        ∃ (_ : IsDiscreteValuationRing R')
          (b : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)),
          Flat b ∧ Surjective b ∧
          GeometricallyReduced
            (DvrPotentialGenericReduction.reducedOver
              ((Over.pullback (Spec.algebraMap R' (FractionRing R'))).obj
                ((Over.pullback b).obj X))).hom

end Langlands.AlgebraicGeometry
