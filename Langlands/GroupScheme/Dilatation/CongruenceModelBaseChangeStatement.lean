import Langlands.GroupScheme.Dilatation.CongruenceModel
import Langlands.GroupScheme.IntegralModel.BaseChange

/-! # Integral points of a congruence model after flat local base change -/

universe u

open AlgebraicGeometry CategoryTheory

namespace Langlands.GroupScheme.IntegralModel

/-- Kaletha–Prasad, Lemma A.5.13(3) and Remark A.5.14, at the flat test ring `A`:
for a flat local extension `R → A` of a DVR with `𝔪_R A = 𝔪_A`, the integral
points of the base change to `A` of the level-`n` congruence model of `M` are
the level-`n` congruence subgroup of the base change of `M`, inside the
`L`-points of `G_L`, for every positive `n`. -/
def CongruenceModelBaseChangeIntegralPointsStatement : Prop :=
  ∀ (R K A L : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] [CommRing A] [IsDomain A]
    [IsLocalRing A] [Field L] [Algebra R A] [Algebra A L] [IsFractionRing A L]
    [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]
    [IsLocalHom (algebraMap R A)] [Module.Flat R A]
    (G : GroupScheme (Spec (CommRingCat.of K))) (M : IntegralModel R K G)
    (_h𝔪 : (IsLocalRing.maximalIdeal R).map (algebraMap R A) = IsLocalRing.maximalIdeal A)
    (ϖ : R) (hϖ : Irreducible ϖ) (n : ℕ+),
    ((M.congruenceModel hϖ (n : ℕ)).baseChange A L).integralPoints =
      (M.baseChange A L).congruenceSubgroupAt n

end Langlands.GroupScheme.IntegralModel
