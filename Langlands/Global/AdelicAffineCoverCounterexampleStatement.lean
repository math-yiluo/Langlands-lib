import Langlands.Global.AdelicAffineCoverCounterexample

/-! # A concrete failure of affine-open coverage on actual adelic points -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- Two actual affine covers of the affine line, with their point-image descriptions. -/
def AffineLineBinaryCoverDescriptionStatement : Prop :=
  ∀ (R : Type u) [CommRing R],
    (∀ b : Bool, IsAffineOpen (affineLineBinaryOpen R b)) ∧
      (⨆ b : Bool, affineLineBinaryOpen R b) = ⊤ ∧
      IsAffineOpen (⊤ : (ringTest R (MvPolynomial Unit R)).left.Opens) ∧
      ∀ (S : Type u) [CommRing S] [Algebra R S],
        affineLineBinaryPointUnion R S =
          {p | IsUnit (affineLinePointEquiv R S p) ∨
            IsUnit (1 - affineLinePointEquiv R S p)} ∧
          affineLineTopPointUnion R S = Set.univ

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- The binary cover omits the explicit full number-field adele point. -/
def NumberFieldAffineCoverCounterexampleStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K],
    numberFieldAffineCoverPoint K ∉ affineLineBinaryPointUnion K (Adeles K) ∧
      affineLineBinaryPointUnion K (Adeles K) ⊂
        affineLineTopPointUnion K (Adeles K)

/-- The same failure occurs for actual function-field adeles with finite constants. -/
def CurvePlaceAffineCoverCounterexampleStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [Finite k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F],
    curvePlaceAffineCoverPoint k F ∉
        affineLineBinaryPointUnion F (CurvePlaceAdeleRing k F) ∧
      affineLineBinaryPointUnion F (CurvePlaceAdeleRing k F) ⊂
        affineLineTopPointUnion F (CurvePlaceAdeleRing k F)

/-- Actual affine-open covers can give different point-image unions over full adeles
in both global-field characteristics. -/
def AdelicAffineCoverCounterexampleStatement : Prop :=
  AffineLineBinaryCoverDescriptionStatement.{u} ∧
    NumberFieldAffineCoverCounterexampleStatement.{u} ∧
    CurvePlaceAffineCoverCounterexampleStatement.{u}

end Langlands.Global
