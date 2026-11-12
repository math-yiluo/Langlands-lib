import Langlands.Global.AdelicLevelModelTopology
import Langlands.AlgebraicGeometry.PointTopology.AffineLinePuncture
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.NumberTheory.FunctionField

/-! # Open immersions on actual arithmetic-level model points -/

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- Function fields: an open immersion into a finite-type model over the `S`-integers induces a
topological embedding on level points, but the open immersion of the punctured affine line into
the affine line has non-open image. -/
def CurvePlaceLevelModelOpenImmersionStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F)),
    (∀ (X Y : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
      (f : X ⟶ Y) [IsOpenImmersion f.left]
      [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom],
      @IsEmbedding
        (RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevel k F S))
        (RingPoint (curvePlaceSIntegers k F S) Y (curvePlaceAdeleLevel k F S))
        (curvePlaceLevelModelPointTopology k F S X)
        (curvePlaceLevelModelPointTopology k F S Y)
        (fun p => p ≫ f)) ∧
    ¬ IsOpen[curvePlaceLevelModelPointTopology k F S
        (ringTest (curvePlaceSIntegers k F S) (MvPolynomial Unit (curvePlaceSIntegers k F S)))]
      (Set.range (fun p : RingPoint (curvePlaceSIntegers k F S)
          (affineLinePuncture (curvePlaceSIntegers k F S)) (curvePlaceAdeleLevel k F S) =>
        (p ≫ affineLinePunctureι (curvePlaceSIntegers k F S) :
          RingPoint (curvePlaceSIntegers k F S)
            (ringTest (curvePlaceSIntegers k F S)
              (MvPolynomial Unit (curvePlaceSIntegers k F S)))
            (curvePlaceAdeleLevel k F S))))

/-- Number fields, with every infinite place: an open immersion into a finite-type model over
the `S`-integers induces a topological embedding on full level points, but the open immersion of
the punctured affine line into the affine line has non-open image. -/
def NumberFieldLevelModelOpenImmersionStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K)),
    (∀ (X Y : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
      (f : X ⟶ Y) [IsOpenImmersion f.left]
      [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom],
      @IsEmbedding
        (RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevel K S))
        (RingPoint ((S : Set (FinitePlace K)).integer K) Y (numberFieldAdeleLevel K S))
        (numberFieldLevelModelPointTopology K S X)
        (numberFieldLevelModelPointTopology K S Y)
        (fun p => p ≫ f)) ∧
    ¬ IsOpen[numberFieldLevelModelPointTopology K S
        (ringTest ((S : Set (FinitePlace K)).integer K)
          (MvPolynomial Unit ((S : Set (FinitePlace K)).integer K)))]
      (Set.range (fun p : RingPoint ((S : Set (FinitePlace K)).integer K)
          (affineLinePuncture ((S : Set (FinitePlace K)).integer K)) (numberFieldAdeleLevel K S) =>
        (p ≫ affineLinePunctureι ((S : Set (FinitePlace K)).integer K) :
          RingPoint ((S : Set (FinitePlace K)).integer K)
            (ringTest ((S : Set (FinitePlace K)).integer K)
              (MvPolynomial Unit ((S : Set (FinitePlace K)).integer K)))
            (numberFieldAdeleLevel K S))))

/-- Conrad's remark after Theorem 3.6 (printed pp.8–9) in both global-field characteristics:
open immersions give topological embeddings of level points, not open embeddings in general. -/
def AdelicLevelModelOpenImmersionStatement : Prop :=
  CurvePlaceLevelModelOpenImmersionStatement.{u} ∧
    NumberFieldLevelModelOpenImmersionStatement.{u}

end Langlands.Global
