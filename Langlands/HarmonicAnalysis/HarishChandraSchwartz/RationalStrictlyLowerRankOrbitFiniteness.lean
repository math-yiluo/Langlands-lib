import Langlands.GroupScheme.Rational.SemistandardProperLeviRank
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLocalOrbitFiniteness
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardOrbitSections

/-! # Strictly lower-rank orbit finiteness for Waldspurger VIII.2 -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.HarishChandraSchwartz

/-- Local VIII.1.2 only for actual relative semisimple ranks strictly below
`n`. The representation-carrier universe is independent of the field universe.
This predicate includes no synthesis-reconstruction assertion. -/
def RationalStrictlyLowerRankOrbitFinitenessStatement (n : ℕ) : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : T.toGrp ⟶ G) (_hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    relativeRootRank i < n →
      RationalLocalDiscreteSeriesOrbitFinitenessStatement.{u, uV} G

/-- Increasing the strict rank bound adds requirements. -/
theorem rationalStrictlyLowerRankOrbitFiniteness_mono {n m : ℕ} (hnm : n ≤ m)
    (h : RationalStrictlyLowerRankOrbitFinitenessStatement.{u, uV} m) :
    RationalStrictlyLowerRankOrbitFinitenessStatement.{u, uV} n := by
  intro F _ _ _ _ G _ _ hG T i hi hlt
  exact h F G hG T i hi (lt_of_lt_of_le hlt hnm)

/-- There is no actual group of relative semisimple rank strictly below zero. -/
theorem rationalStrictlyLowerRankOrbitFiniteness_zero :
    RationalStrictlyLowerRankOrbitFinitenessStatement.{u, uV} 0 := by
  intro F _ _ _ _ G _ _ hG T i hi hlt
  exact (Nat.not_lt_zero _ hlt).elim

section Specialization

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}

/-- Apply the strict-rank premise at one actual connected reductive group. -/
theorem rationalLocalOrbitFiniteness_of_rank_lt {n : ℕ}
    (h : RationalStrictlyLowerRankOrbitFinitenessStatement.{u, uV} n)
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hlt : haveI := hG.isAffineHom; relativeRootRank i < n) :
    RationalLocalDiscreteSeriesOrbitFinitenessStatement.{u, uV} G :=
  h F G hG T i hi hlt

/-- Every closed reductive model of a literal proper Levi lies within the
strict-rank premise, using the inherited ambient maximal split torus.
No orbit-finiteness assumption at the ambient group occurs. -/
theorem rationalLocalOrbitFiniteness_properLevi_of_lowerRank
    (hrank : SemistandardProperLeviRankStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (h : haveI := hG.isAffineHom
      RationalStrictlyLowerRankOrbitFinitenessStatement.{u, uV} (relativeRootRank i))
    (p : SemistandardSpectralIndex i) (hp : p.parabolic ≠ ⊤)
    (m : RationalSemistandard.LeviModel p) :
    haveI := m.reductive.isAffineHom
    haveI : IsAffine m.scheme.X.left := isAffine_of_isAffineHom m.scheme.X.hom
    haveI := m.reductive.smooth
    RationalLocalDiscreteSeriesOrbitFinitenessStatement.{u, uV} m.scheme := by
  let := hG.isAffineHom
  let := m.reductive.isAffineHom
  let : IsAffine m.scheme.X.left := isAffine_of_isAffineHom m.scheme.X.hom
  let := m.reductive.smooth
  exact h F m.scheme m.reductive T
    (semistandardLeviSplitTorus p m.represents)
    (isMaximalSplitTorus_semistandardLeviSplitTorus p m.represents m.closed hi)
    (hrank F G hG T i hi p hp m.scheme m.inclusion m.represents m.closed m.reductive)

/-- The specialization can equally use any maximal split torus in the same
literal proper Levi model; the rank comparison already accounts for the change. -/
theorem rationalLocalOrbitFiniteness_properLevi_of_lowerRank_at_torus
    (hrank : SemistandardProperLeviRankStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (h : haveI := hG.isAffineHom
      RationalStrictlyLowerRankOrbitFinitenessStatement.{u, uV} (relativeRootRank i))
    (p : SemistandardSpectralIndex i) (hp : p.parabolic ≠ ⊤)
    (m : RationalSemistandard.LeviModel p)
    {T' : CommGroupScheme (Spec (CommRingCat.of F))}
    (a : T'.toGrp ⟶ m.scheme) (ha : IsMaximalSplitTorus a) :
    haveI := m.reductive.isAffineHom
    haveI : IsAffine m.scheme.X.left := isAffine_of_isAffineHom m.scheme.X.hom
    haveI := m.reductive.smooth
    RationalLocalDiscreteSeriesOrbitFinitenessStatement.{u, uV} m.scheme := by
  let := hG.isAffineHom
  let := m.reductive.isAffineHom
  let : IsAffine m.scheme.X.left := isAffine_of_isAffineHom m.scheme.X.hom
  let := m.reductive.smooth
  exact h F m.scheme m.reductive T' a ha
    (relativeRootRank_properLevi_lt hrank hG hi p hp m.represents m.closed
      m.reductive a ha)

end Specialization

end Langlands.HarishChandraSchwartz
