import Langlands.AbelianScheme.PolarizedFiniteLevel.CanonicalBundle
import Langlands.AlgebraicGeometry.ProjectiveSpace.TwistOne
import Mathlib.SetTheory.Cardinal.Finite

/-! # The actual torsion-hyperplane count for a supplied cubic embedding -/

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry GroupScheme.Tate

universe u

/-- A supplied nondegenerate closed embedding by the actual canonical cubic
bundle has the uniform torsion-hyperplane count used in the covariant argument.
This proposition neither constructs the embedding nor proves the count. -/
def CubicTorsionHyperplaneBoundStatement : Prop :=
  ∀ (P : Prerequisites.{u}) (K : Type u) [Field K] [IsAlgClosed K]
    (g d n : ℕ), 0 < g → 0 < d → 0 < n → (n : K) ≠ 0 →
      ∀ (a : Datum P (Spec (CommRingCat.of K)) g d n)
        (m : ℕ) (i : a.abelian.X.left ⟶ ProjectiveSpace K m),
        IsClosedImmersion i →
        i ≫ projectiveSpaceToSpec K m = a.abelian.X.hom →
        Nonempty ((Scheme.Modules.pullback i).obj (twistOne K m) ≅ a.cubicBundle.obj) →
        (∀ f : projectiveSpaceGrading K m 1, (f : ProjectiveCoordinateRing K m) ≠ 0 →
          ∃ x : a.abelian.X.left,
            (f : ProjectiveCoordinateRing K m) ∉ (i x).asHomogeneousIdeal) →
        ∀ f : projectiveSpaceGrading K m 1, (f : ProjectiveCoordinateRing K m) ≠ 0 →
          Nat.card {x : Level a.abelian.toGrp (Over.mk (𝟙 (Spec (CommRingCat.of K)))) n //
            (f : ProjectiveCoordinateRing K m) ∈
              (i ((Additive.toMul x).val.left (IsLocalRing.closedPoint K))).asHomogeneousIdeal} ≤
            6 ^ g * d * Nat.factorial g * n ^ (2 * g - 2)

end Langlands.AbelianScheme.PolarizedFiniteLevel
