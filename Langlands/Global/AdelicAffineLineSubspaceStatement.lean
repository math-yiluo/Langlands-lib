import Langlands.Global.AdeleProductSubspaceTopology
import Langlands.Global.ProjectiveAffineChart
import Mathlib.NumberTheory.FunctionField

/-! # The standard affine line in adelic projective one-space -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

/-- The affine-line adelic carrier has the full-product subspace topology when
viewed inside the actual projective-line adelic point space. -/
def CurvePlaceAffineLineSubspaceStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [Finite k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F)),
    letI := curvePlaceProductSubspaceAdeleTopology k F
    letI := curvePlaceProjectiveAdelePointTopology k F S 1
    IsEmbedding (projectiveLineAffinePoint F (CurvePlaceAdeleRing k F))

/-- The corresponding full number-field assertion, including every infinite place. -/
def NumberFieldAffineLineSubspaceStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K)),
    letI := numberFieldProductSubspaceAdeleTopology K
    letI := numberFieldProjectiveAdelePointTopology K S 1
    IsEmbedding (projectiveLineAffinePoint K (Adeles K))

/-- The affine-line subspace-topology assertion of Conrad Example 4.3 in both
characteristics, on the original adelic carriers and actual projective points. -/
def AdelicAffineLineSubspaceStatement : Prop :=
  CurvePlaceAffineLineSubspaceStatement.{u} ∧ NumberFieldAffineLineSubspaceStatement.{u}

end Langlands.Global
