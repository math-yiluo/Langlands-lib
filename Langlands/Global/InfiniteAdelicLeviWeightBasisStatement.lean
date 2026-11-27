import Langlands.Global.InfiniteAdelicGroupManifold
import Langlands.Geometry.Manifold.SmoothGroupConjugation
import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Reductive.Basic

/-! # A weight basis of the archimedean Lie algebra adapted to a parabolic

For a parabolic `Q = M'V` of a connected reductive group `G` over a number field `F`, the real Lie
algebra of `G(F_∞)` has a basis of eigenvectors of `Ad(t)` for a point `t` of `M'(F_∞)` (the value
at `2` of a central cocharacter of `M'` presenting `Q`), with eigenvalues `2 ^ w` for integer
weights `w`. The weight-zero vectors span the image of the Lie algebra of `M'(F_∞)` and the
positive-weight vectors span the tangent directions of `V(F_∞)`. This file states this. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Geometry.Manifold InfiniteAdelicGroupPoints

/-- A weight basis of the archimedean Lie algebra adapted to a parabolic (Conrad–Gabber–Prasad,
Proposition 2.1.8; Milne, Theorem 25.1). Let `G` be connected reductive over a number field `F`,
`q : Q → G` a parabolic subgroup with geometric unipotent radical `iV : V → Q` and rational Levi
subgroup `l' : M' → Q`, and fix smooth structures on `G` and `M'`. Write `ι` for the point map
`M'(F_∞) → G(F_∞)` of `l' ≫ q` and `S_V` for the image of `V(F_∞)` in `G(F_∞)`. There are
`t ∈ M'(F_∞)` and a real basis `b` of the Lie algebra of `G(F_∞)` with integer weights `w` such
that `Ad(ι t) (b a) = 2 ^ (w a) • b a`; the tangent map of `ι` at `1` is injective; its range
contains every `b a` with `w a = 0` and lies in their span; every `b a` with `w a > 0` is the
velocity at `0` of a smooth curve through `1` in `S_V`; and the velocity at `0` of every such
curve lies in the span of the `b a` with `w a > 0`. -/
def LeviTangentWeightBasisStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G Q M' V : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [IsAffine Q.X.left] [IsAffine M'.X.left]
    (q : Q ⟶ G) (iV : V ⟶ Q) (l' : M' ⟶ Q),
    IsConnectedReductive G → IsParabolicSubgroup q →
    LeviSubgroup.IsGeometricUnipotentRadical iV → IsRationalLeviSubgroup l' →
    ∀ {d d' : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hsmooth' : SmoothOfRelativeDimension d' M'.X.hom),
      let Ainf := CommAlgCat.of F (InfiniteAdeleRing F)
      let ιQ : InfiniteAdelicGroupPoints F M' → InfiniteAdelicGroupPoints F G :=
        M'.affinePointsTarget (l' ≫ q) Ainf
      let SV : Set (InfiniteAdelicGroupPoints F G) :=
        Set.range (V.affinePointsTarget (iV ≫ q) Ainf)
      letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hsmooth
      letI := smoothChartedSpace F M' hsmooth'
      letI := smoothLieGroup F G hsmooth
      ∃ (t : InfiniteAdelicGroupPoints F M') (n : ℕ)
        (b : Module.Basis (Fin n) ℝ
          (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)))
        (w : Fin n → ℤ),
        (∀ a, groupTangentConjugation 𝓘(ℝ, smoothModel F d) (ιQ t) (b a) =
          ((2 : ℝ) ^ w a) • b a) ∧
        Function.Injective (mfderiv 𝓘(ℝ, smoothModel F d') 𝓘(ℝ, smoothModel F d) ιQ 1) ∧
        (∀ a, w a = 0 →
          b a ∈ Set.range (mfderiv 𝓘(ℝ, smoothModel F d') 𝓘(ℝ, smoothModel F d) ιQ 1)) ∧
        (∀ Y : TangentSpace 𝓘(ℝ, smoothModel F d') (1 : InfiniteAdelicGroupPoints F M'),
          mfderiv 𝓘(ℝ, smoothModel F d') 𝓘(ℝ, smoothModel F d) ιQ 1 Y ∈
            Submodule.span ℝ (b '' {a | w a = 0})) ∧
        (∀ a, 0 < w a → ∃ c : ℝ → InfiniteAdelicGroupPoints F G,
          ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, smoothModel F d) ∞ c ∧ c 0 = 1 ∧ (∀ s, c s ∈ SV) ∧
            mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, smoothModel F d) c 0 (1 : ℝ) = b a) ∧
        (∀ c : ℝ → InfiniteAdelicGroupPoints F G,
          ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, smoothModel F d) ∞ c → c 0 = 1 → (∀ s, c s ∈ SV) →
            mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, smoothModel F d) c 0 (1 : ℝ) ∈
              Submodule.span ℝ (b '' {a | 0 < w a}))

end Langlands.Global
