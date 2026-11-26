import Langlands.Global.InfiniteAdelicGroupManifold
import Langlands.GroupScheme.Rational.LeviSubgroup
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.Algebra.Lie.Solvable
import Mathlib.Geometry.Manifold.GroupLieAlgebra

/-! # The complexified archimedean tangent of a rational parabolic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.InfiniteAdelicGroupPoints Langlands.GroupScheme

variable (F : Type u) [Field F] [NumberField F]

/-- The complexified identity tangent Lie algebra of the actual infinite adelic points,
for the atlas chosen by `hsmooth`. -/
abbrev AdelicComplexLieAlgebra (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom) :=
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)

/-- The complexified derivative at the identity of the map of actual infinite adelic points
induced by a homomorphism of group schemes. -/
def complexPointDifferential {G H : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine G.X.left] [IsAffine H.X.left] {d e : ℕ}
    (hH : SmoothOfRelativeDimension e H.X.hom) (hG : SmoothOfRelativeDimension d G.X.hom)
    (f : H ⟶ G) :
    AdelicComplexLieAlgebra F H hH →ₗ[ℂ] AdelicComplexLieAlgebra F G hG := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hG
  letI := smoothChartedSpace F H hH
  exact LinearMap.baseChange ℂ
    (mfderiv 𝓘(ℝ, smoothModel F e) 𝓘(ℝ, smoothModel F d)
      (H.affinePointsTarget f (CommAlgCat.of F (InfiniteAdeleRing F)))
      (1 : InfiniteAdelicGroupPoints F H)).toLinearMap

/-- **The archimedean tangent grading of a rational parabolic.** For a connected reductive
group over a number field with a parabolic subgroup, its geometric unipotent radical and a
rational Levi, the complexified tangent Lie algebra of the infinite adelic points is reductive,
and some element `H` acts on it diagonalizably with integer eigenvalues such that the
complexified derivative of the Levi is injective with image the centralizer of `H`, and the
complexified derivative of the radical has image the span of the eigenvectors with positive
eigenvalues. -/
def ParabolicLeviTangentGradingStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G Q M V : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [IsAffine M.X.left] [IsAffine V.X.left]
    (q : Q ⟶ G) (iV : V ⟶ Q) (l : M ⟶ Q),
    IsConnectedReductive G → IsParabolicSubgroup q →
    LeviSubgroup.IsGeometricUnipotentRadical iV → IsRationalLeviSubgroup l →
    IsIso (subgroupMultiplication l iV) →
    ∀ {d e c : ℕ} (hG : SmoothOfRelativeDimension d G.X.hom)
      (hM : SmoothOfRelativeDimension e M.X.hom) (hV : SmoothOfRelativeDimension c V.X.hom),
      letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hG
      letI := smoothLieGroup F G hG
      letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
        (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
      LieAlgebra.radical ℂ (AdelicComplexLieAlgebra F G hG) =
          LieAlgebra.center ℂ (AdelicComplexLieAlgebra F G hG) ∧
      ∃ H : AdelicComplexLieAlgebra F G hG,
        Submodule.span ℂ {Y : AdelicComplexLieAlgebra F G hG |
          ∃ k : ℤ, ⁅H, Y⁆ = (k : ℂ) • Y} = ⊤ ∧
        Function.Injective (complexPointDifferential F hM hG (l ≫ q)) ∧
        (∀ Y : AdelicComplexLieAlgebra F G hG,
          Y ∈ LinearMap.range (complexPointDifferential F hM hG (l ≫ q)) ↔ ⁅H, Y⁆ = 0) ∧
        LinearMap.range (complexPointDifferential F hV hG (iV ≫ q)) =
          Submodule.span ℂ {Y : AdelicComplexLieAlgebra F G hG |
            ∃ k : ℕ, ⁅H, Y⁆ = ((k + 1 : ℕ) : ℂ) • Y}

end Langlands.Automorphic.GroupSchemeFunctions
