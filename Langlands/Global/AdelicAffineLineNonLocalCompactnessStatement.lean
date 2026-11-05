import Langlands.Global.AdelicAffineLineSubspaceStatement

/-! # Non-local-compactness of the adelic affine-line subspace -/

noncomputable section

universe u

namespace Langlands.Global

/-- The product-induced adelic topology and the actual projective affine-line
subspace are not locally compact, over a global function field. -/
def CurvePlaceAffineLineNonLocalCompactnessStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [Finite k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F)),
    letI := curvePlaceProductSubspaceAdeleTopology k F
    letI := curvePlaceProjectiveAdelePointTopology k F S 1
    (¬ LocallyCompactSpace (CurvePlaceAdeleRing k F)) ∧
      ¬ LocallyCompactSpace (Set.range
        (projectiveLineAffinePoint F (CurvePlaceAdeleRing k F)))

/-- The full number-field assertion, with every infinite factor retained. -/
def NumberFieldAffineLineNonLocalCompactnessStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K)),
    letI := numberFieldProductSubspaceAdeleTopology K
    letI := numberFieldProjectiveAdelePointTopology K S 1
    (¬ LocallyCompactSpace (Adeles K)) ∧
      ¬ LocallyCompactSpace (Set.range (projectiveLineAffinePoint K (Adeles K)))

/-- Conrad Example 4.3: the adelic affine line inside adelic projective one-space
is not locally compact, in both global-field characteristics. -/
def AdelicAffineLineNonLocalCompactnessStatement : Prop :=
  CurvePlaceAffineLineNonLocalCompactnessStatement.{u} ∧
    NumberFieldAffineLineNonLocalCompactnessStatement.{u}

end Langlands.Global
