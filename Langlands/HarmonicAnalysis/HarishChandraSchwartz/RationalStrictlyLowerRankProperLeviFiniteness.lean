import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalStrictlyLowerRankOrbitFiniteness
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardThetaFixed

/-! # Packaging strictly lower-rank finiteness on the proper Levis -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.HarishChandraSchwartz

/-- The rank-restricted local VIII.1.2 input supplies exactly the proper-Levi
premise used by the proper support interface. The structural rank-decrease
target is retained separately in the theorem establishing this implication. -/
def RationalStrictlyLowerRankProperLeviFinitenessStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : T.toGrp ⟶ G) (_hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    RationalStrictlyLowerRankOrbitFinitenessStatement.{u, uV} (relativeRootRank i) →
      RationalSemistandard.ProperLeviOrbitFiniteness.{u, uV} (i := i)

section Specialization

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}

/-- Package the already established pointwise specialization, keeping every
closed reductive model of every literal proper Levi. -/
theorem properLeviOrbitFiniteness_of_strictlyLowerRank
    (hrank : SemistandardProperLeviRankStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (h : haveI := hG.isAffineHom
      RationalStrictlyLowerRankOrbitFinitenessStatement.{u, uV} (relativeRootRank i)) :
    RationalSemistandard.ProperLeviOrbitFiniteness.{u, uV} (i := i) := by
  intro p hp m
  exact rationalLocalOrbitFiniteness_properLevi_of_lowerRank hrank hG hi h p hp m

/-- At relative semisimple rank zero, the proper-Levi premise is vacuous
under the exact structural rank comparison; no analytic premise is needed. -/
theorem properLeviOrbitFiniteness_of_rank_zero
    (hrank : SemistandardProperLeviRankStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hzero : haveI := hG.isAffineHom; relativeRootRank i = 0) :
    RationalSemistandard.ProperLeviOrbitFiniteness.{u, uV} (i := i) := by
  intro p hp _
  exact (hp (semistandardParabolic_eq_top_of_rank_zero hrank hG hi hzero p)).elim

end Specialization

/-- The proper support interface uses only strictly lower-rank local
finiteness, conditional on the exact actual proper-Levi rank decrease. -/
theorem rationalStrictlyLowerRankProperLeviFiniteness
    (hrank : SemistandardProperLeviRankStatement.{u}) :
    RationalStrictlyLowerRankProperLeviFinitenessStatement.{u, uV} := by
  intro F _ _ _ _ G hG T i hi h
  exact properLeviOrbitFiniteness_of_strictlyLowerRank hrank hG hi h

end Langlands.HarishChandraSchwartz
