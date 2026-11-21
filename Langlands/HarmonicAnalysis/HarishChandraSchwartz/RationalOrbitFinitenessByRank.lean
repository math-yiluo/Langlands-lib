import Langlands.GroupScheme.Rational.CentralizerRootSupport
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicConjugacyAssembly
import Langlands.GroupScheme.Rational.SplitTorusRationalRank
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalRankZeroOrbitFiniteness
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalStrictlyLowerRankProperLeviFiniteness

/-! # Discrete-series orbit finiteness by relative semisimple rank -/

universe u uV

open AlgebraicGeometry CategoryTheory
open Langlands.GroupScheme

namespace Langlands.HarishChandraSchwartz

/-- Local VIII.1.2 for all connected reductive groups of the given relative
semisimple rank, measured using a maximal split torus. -/
def RationalExactRankDiscreteSeriesOrbitFinitenessStatement (n : ℕ) : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G),
    IsMaximalSplitTorus i →
    haveI := hG.isAffineHom
    relativeRootRank i = n → RationalLocalDiscreteSeriesOrbitFinitenessStatement.{u, uV} G

/-- Extending the strict bound by one adds exactly the groups of rank `n`. -/
theorem rationalStrictlyLowerRankOrbitFiniteness_succ_iff {n : ℕ} :
    RationalStrictlyLowerRankOrbitFinitenessStatement.{u, uV} (n + 1) ↔
      RationalStrictlyLowerRankOrbitFinitenessStatement.{u, uV} n ∧
        RationalExactRankDiscreteSeriesOrbitFinitenessStatement.{u, uV} n := by
  constructor
  · intro h
    refine ⟨rationalStrictlyLowerRankOrbitFiniteness_mono (Nat.le_succ n) h, ?_⟩
    intro F _ _ _ _ G _ _ hG T i hi hrank
    exact h F G hG T i hi (Nat.lt_succ_iff_lt_or_eq.mpr (Or.inr hrank))
  · rintro ⟨hlower, hexact⟩ F _ _ _ _ G _ _ hG T i hi hrank
    rcases Nat.lt_succ_iff_lt_or_eq.mp hrank with hlt | heq
    · exact hlower F G hG T i hi hlt
    · exact hexact F G hG T i hi heq

/-- The strict bound one is the named rank-zero finiteness target. -/
theorem rationalStrictlyLowerRankOrbitFiniteness_one_iff :
    RationalStrictlyLowerRankOrbitFinitenessStatement.{u, uV} 1 ↔
      RationalRankZeroDiscreteSeriesOrbitFinitenessStatement.{u, uV} :=
  (rationalStrictlyLowerRankOrbitFiniteness_succ_iff (n := 0)).trans
    (and_iff_right rationalStrictlyLowerRankOrbitFiniteness_zero)

/-- Orbit finiteness on every strict rank bound gives the global VIII.1.2
statement by choosing an actual maximal split torus of each group. -/
theorem rationalDiscreteSeriesOrbitFiniteness_iff_all_rank_bounds :
    RationalDiscreteSeriesOrbitFinitenessStatement.{u, uV} ↔
      ∀ n, RationalStrictlyLowerRankOrbitFinitenessStatement.{u, uV} n := by
  constructor
  · intro h _ F _ _ _ _ G _ _ hG _ _ _ _
    exact h F G hG
  · intro h F _ _ _ _ G _ _ hG
    let := hG.isAffineHom
    obtain ⟨T, i, hi⟩ := exists_maximalSplitTorus G
    exact h (relativeRootRank i + 1) F G hG T i hi (Nat.lt_succ_self _)

/-- A bound covering the ambient rank also covers every semistandard Levi
model, giving the all-Levi finiteness premise of VIII.1.3. -/
theorem RationalSemistandard.allLeviOrbitFiniteness_of_rank_lt
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))}
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) {n : ℕ}
    (hfin : RationalStrictlyLowerRankOrbitFinitenessStatement.{u, uV} n)
    (hrank : haveI := hG.isAffineHom; relativeRootRank i < n) :
    RationalSemistandard.AllLeviOrbitFiniteness.{u, uV} (i := i) := by
  let := hG.isAffineHom
  intro p m
  let := m.reductive.isAffineHom
  let : IsAffine m.scheme.X.left := isAffine_of_isAffineHom m.scheme.X.hom
  let := m.reductive.smooth
  let j := semistandardLeviSplitTorus p m.represents
  have hj := isMaximalSplitTorus_semistandardLeviSplitTorus p m.represents m.closed hi
  let := hi.isSplitSubtorus.1.finite_relativeRootSpan i
  have hspan : relativeRootSpan j ≤ relativeRootSpan i :=
    Submodule.span_mono (Set.image_mono
      (relativeRoots_subset_of_factor m.represents j
        (semistandardLeviSplitTorus_comp p m.represents)))
  have hle : relativeRootRank j ≤ relativeRootRank i := Submodule.finrank_mono hspan
  exact hfin F m.scheme m.reductive T j hj (lt_of_le_of_lt hle hrank)

end Langlands.HarishChandraSchwartz
