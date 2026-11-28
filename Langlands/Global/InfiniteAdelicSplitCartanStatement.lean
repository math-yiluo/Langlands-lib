import Langlands.Global.InfiniteAdelicLeviEnveloping
import Langlands.GroupScheme.Torus.Maximal
import Langlands.Algebra.HarishChandra.ParabolicIndependenceStatement

/-! # A split Cartan subalgebra and a parabolic element of the complexified Lie algebra of `G(F_∞)`

For a connected reductive group `G` over a number field `F`, a parabolic subgroup `Q = M' ⋉ V`
with a rational Levi subgroup `M'`, and a maximal torus `T` of `M'` over `F`, this file states:
the complex span `𝔥` of the tangent directions of `T(F_∞)` in `ℂ ⊗_ℝ Lie G(F_∞)` is a split
Cartan subalgebra in the sense of `IsSplitCartan`, and some `X ∈ 𝔥` has integer eigenvalues
under `ad`, with kernel the complexified Lie algebra of `M'(F_∞)` and positive eigenspaces
spanning that of `V(F_∞)`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  InfiniteAdelicGroupPoints Langlands.Algebra.HarishChandra

/-- Split Cartan subalgebra and parabolic element at infinity. Let `G` be connected reductive
over a number field `F` with a smooth structure of relative dimension `d`, `q : Q → G` a
parabolic subgroup with geometric unipotent radical `iV : V → Q` and rational Levi subgroup
`l' : M' → Q`, and `t : T → M'` a maximal torus of `M'` over `F`. For a subset `S` of `G(F_∞)`
write `𝔰(S)` for the complex span of the vectors `1 ⊗ X` in `ℂ ⊗_ℝ Lie G(F_∞)`, with `X` a curve
tangent at `1` of `S`. Then `𝔰` of the image of `T(F_∞)` is the underlying subspace of a Lie
subalgebra `𝔥` with `IsSplitCartan 𝔥`, and some `X ∈ 𝔥` satisfies:
every eigenvalue of `ad X` is an integer, `ker (ad X)` is `𝔰` of the image of `M'(F_∞)`, and
the sum of the eigenspaces of `ad X` for the positive integers is `𝔰` of the image of
`V(F_∞)`. -/
def InfiniteAdelicSplitCartanStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G Q M' V : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [IsAffine Q.X.left] [LocallyOfFiniteType Q.X.hom] [IsAffine M'.X.left]
    (q : Q ⟶ G) (iV : V ⟶ Q) (l' : M' ⟶ Q)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (t : T.toGrp ⟶ M'),
    IsConnectedReductive G → IsParabolicSubgroup q →
    LeviSubgroup.IsGeometricUnipotentRadical iV → IsRationalLeviSubgroup l' →
    IsMaximalTorus t →
    ∀ {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom),
      let Ainf := CommAlgCat.of F (InfiniteAdeleRing F)
      letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hsmooth
      letI := smoothLieGroup F G hsmooth
      letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
        (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
      let tangentSpan : Set (InfiniteAdelicGroupPoints F G) → Submodule ℂ
          (ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)) :=
        fun S => Submodule.span ℂ ((fun X => (1 : ℂ) ⊗ₜ[ℝ] X) '' curveTangents F hsmooth S)
      ∃ H : LieSubalgebra ℂ
          (ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)),
        H.toSubmodule = tangentSpan
            (Set.range (GroupScheme.affinePointsTarget (G := T.toGrp) (t ≫ l' ≫ q) Ainf)) ∧
        IsSplitCartan H ∧
        ∃ X ∈ H,
          (∀ c : ℂ, (LieAlgebra.ad ℂ _ X).eigenspace c ≠ ⊥ → ∃ n : ℤ, c = n) ∧
          LinearMap.ker (LieAlgebra.ad ℂ _ X) =
            tangentSpan (Set.range (M'.affinePointsTarget (l' ≫ q) Ainf)) ∧
          positiveEigenSubmodule X = tangentSpan (Set.range (V.affinePointsTarget (iV ≫ q) Ainf))

end Langlands.Global
