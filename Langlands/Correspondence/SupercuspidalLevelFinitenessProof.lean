import Langlands.Correspondence.SupercuspidalFinitenessStatement

/-!
# Reduction of bounded-level supercuspidal finiteness

The published compact open last-row subgroups and fixed-level stratum
identity give the existing reduction statement over every nonarchimedean
local field in its stated domain.
-/

namespace Langlands.Henniart

universe uF uV

/-- Bounded-level finiteness follows from compact-open finiteness. -/
theorem supercuspidalLevelFinitenessReduction :
    SupercuspidalLevelFinitenessReductionStatement.{uF, uV} := by
  intro hcompact F _ _ _ _ n χ b
  rw [GeneralLinear.SupercuspidalClass.centralLevelStratum_eq χ b]
  exact hcompact F n χ (Conductor.levelOpenSubgroup F n b)
    (Conductor.isCompact_levelOpenSubgroup F n b)

/-- The full finiteness family reduces to its compact-open assertion. -/
theorem supercuspidalFiniteness_of_compactOpenFiniteness
    (hcompact : SupercuspidalCompactOpenFinitenessStatement.{uF, uV}) :
    SupercuspidalFinitenessStatement.{uF, uV} :=
  ⟨hcompact, supercuspidalLevelFinitenessReduction hcompact,
    supercuspidalLevelFinitenessReduction⟩

end Langlands.Henniart
