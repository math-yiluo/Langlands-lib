import Langlands.Global.GlobalPlaceTopologyFacts
import Langlands.AlgebraicGeometry.PointTopology.AffineLinePunctureUnits

/-! # Failure of embedding for actual adelic punctured-line points -/

noncomputable section

universe u

open CategoryTheory Topology

namespace Langlands.AlgebraicGeometry.PointTopology

/-- Three forms of the unit-inclusion obstruction for a topological value ring. -/
def AffineLinePunctureEmbeddingObstruction (S : Type u)
    [CommRing S] [TopologicalSpace S] : Prop :=
  ¬ @IsTopologicalGroup Sˣ (TopologicalSpace.induced (Units.val : Sˣ → S) inferInstance) _ ∧
    ¬ IsEmbedding (Units.val : Sˣ → S) ∧
    ∀ (R : Type u) [CommRing R] [Algebra R S],
      ¬ IsEmbedding (X := RingPoint R (affineLinePuncture R) S)
        (Y := RingPoint R (ringTest R (MvPolynomial Unit R)) S)
        (fun p => p ≫ affineLinePunctureι R)

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- The obstruction in the original full number-field adelic topology. -/
def NumberFieldPunctureEmbeddingStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K],
    AffineLinePunctureEmbeddingObstruction (Adeles K)

/-- The obstruction for actual curve-place adeles over arbitrary constants. -/
def CurvePlacePunctureEmbeddingStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F],
    AffineLinePunctureEmbeddingObstruction (CurvePlaceAdeleRing k F)

/-- Conrad's nonembedding of punctured-line points in both global-field characteristics. -/
def AdelicPunctureEmbeddingStatement : Prop :=
  NumberFieldPunctureEmbeddingStatement.{u} ∧ CurvePlacePunctureEmbeddingStatement.{u}

end Langlands.Global
