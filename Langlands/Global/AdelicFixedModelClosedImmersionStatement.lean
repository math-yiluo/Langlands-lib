import Langlands.Global.AdelicFixedModelCocone
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.NumberTheory.FunctionField

/-! # Closed immersions on actual full-adele fixed-model points -/

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- Closed model immersions give closed embeddings for the actual full-adele
final topologies, including nonaffine models and both global-field cases. -/
def AdelicFixedModelClosedImmersionStatement : Prop :=
  (∀ (k F : Type u) [Field k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (X Y : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    (f : X ⟶ Y) [IsClosedImmersion f.left]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom],
    @IsClosedEmbedding
      (CurvePlaceFixedModelAdelePoints k F S X)
      (CurvePlaceFixedModelAdelePoints k F S Y)
      (curvePlaceFixedModelAdelePointTopology k F S X)
      (curvePlaceFixedModelAdelePointTopology k F S Y)
      (fun p => p ≫ f)) ∧
  (∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    (X Y : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    (f : X ⟶ Y) [IsClosedImmersion f.left]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom],
    @IsClosedEmbedding
      (NumberFieldFixedModelAdelePoints K S X)
      (NumberFieldFixedModelAdelePoints K S Y)
      (numberFieldFixedModelAdelePointTopology K S X)
      (numberFieldFixedModelAdelePointTopology K S Y)
      (fun p => p ≫ f))

end Langlands.Global
