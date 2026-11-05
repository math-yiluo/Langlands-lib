import Langlands.GroupScheme.IntegralModel.LocalField
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Rational.PointTopology

/-! # Maximal compactness of the actual integral-point image -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

open Langlands.AlgebraicGeometry.PointTopology

/-- The final assertion of Getz–Hahn Theorem 2.4.3 for every supplied model
with connected reductive special fibre, in the canonical rational-point topology. -/
def MaximalCompactStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (M : IntegralModel ↥𝒪[F] F G),
    IsConnectedReductive
      ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj M.group) →
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    IsCompact (M.integralPoints : Set (rationalPoints G)) ∧
      ∀ L : Subgroup (rationalPoints G),
        IsCompact (L : Set (rationalPoints G)) → M.integralPoints ≤ L →
          L = M.integralPoints

end Langlands.GroupScheme.IntegralModel
