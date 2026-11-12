# Proper-standard induction exclusion inside a Levi from the whole-category splitting

Author: Worker 174, Task 5323 (`c79b0cd0-661f-4239-9f65-483d6f319480`).

Module `Langlands.Representation.Aubert.General.RationalLeviInductionExclusionFromWhole`,
namespace `Langlands.Aubert.General.RationalPointFamily`.

This module derives the second extraction input,
`PointLeviStandardInductionCuspidalExclusion` of
[RationalCuspidalExtractionInputs](RationalCuspidalExtractionInputs.md), from
the published whole-category cuspidal splitting
`Langlands.CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement`
(Renard VI.3.5, module
[RationalWholeCuspidalDecompositionStatement](../../CuspidalSupport/RationalWholeCuspidalDecompositionStatement.md)).
That splitting is **not proved** in the Library; it remains an explicit
hypothesis of every theorem here. Nothing in this module proves Renard VI.5.2
or VI.3.5 unconditionally.

## Declarations

`pointLeviStandardInductionCuspidalExclusion_of_wholeStatement` assumes
`RationalWholeCuspidalCategoryDecompositionStatement.{u, max (u + 1) v}`, the
splitting at the carrier universe `max (u + 1) v` of the representations
involved. At the displayed data (a nonarchimedean local field `k`, an actual
connected reductive `G`, an actual maximal split torus `i` and generic
cocharacter `ν`, the canonical locally compact nonarchimedean point topology,
`StandardCocharacterStatement`, `StandardLeviIntersectionStatement`, closed
actual standard Levis and radicals) it proves
`PointLeviStandardInductionCuspidalExclusion i ν hInter hG hi hν hM hU`.
That is: for every standard `J`, every proper subset `K ≠ univ` of `J`, every
smooth `ρ` of the fine Levi `(levi i ν (leviIndex J K)).subgroupOf (levi i ν J)`
and every irreducible `τ` of `levi i ν J` satisfying the published inside-Levi
`IsLeviCuspidal`, `τ` is not an actual `SmoothRep.IsSubquotient` of the actual
normalized induction of `ρ` inside `levi i ν J`. Neither `ρ` nor the
ambient induction carries a finiteness or irreducibility condition.

`rationalCuspidalExtractionInputs_of_wholeStatement` assumes the same
splitting and proves the whole published `RationalCuspidalExtractionInputsStatement.{u, v}`:
its first conjunct is `exists_pointInducedJacquetGeometricFiltration` from
[RationalInducedJacquetGeometricFiltration](RationalInducedJacquetGeometricFiltration.md)
(no extra hypothesis), and its second conjunct is the preceding theorem. The
proof introduces the binders of the statement exactly, installs
`hG.isAffineHom`, `hi.isSplitSubtorus.mono`, `pointTopology` and
`simpleRelativeRootFintype`, and applies the two theorems. Together with the
published `rationalCuspidalJacquetFactorExtraction_of_inputs` this reduces the
extraction target to the splitting; that composite is not stated here.

## Proof of the exclusion

Fix `J`, a proper `K`, `ρ`, and an irreducible inside-Levi cuspidal `τ` with
`τ` a subquotient of `i^{M_J}_K(ρ)`.

1. Worker 1570's `hasLeviCuspidalRemainderSplitting_of_wholeStatement`
   (module [RationalLeviSplittingFromWhole](../../CuspidalSupport/RationalLeviSplittingFromWhole.md))
   applies the whole-category statement to the actual standard Levi scheme of
   `J` and transports the resulting coproduct to the literal subgroup
   `levi i ν J`. Applied to the object `i^{M_J}_K(ρ)`, it gives
   `HasLeviCuspidalRemainderSplitting`: an actual Boolean coproduct whose
   `true` component is cuspidal for the proper inside-Levi standard tests and
   whose `false` component has no nonzero cuspidal subquotient. Its one
   remaining input, a relative root system for the intrinsic maximal split
   torus of the Levi scheme, is supplied by the published
   `Langlands.GroupScheme.relativeRootSystem`, with connected reductivity of
   the Levi scheme from `standardLeviScheme_isConnectedReductive` and
   `Langlands.GroupScheme.dynamicCentralizerReductive`, and maximality of its
   torus factor from `IsMaximalSplitTorus.isMaximalSplitTorus_standardLeviTorusFactor`.
   This is the same supply used by the published
   `rationalLeviJacquetSplitting_of_wholeDecomposition`.
2. The published `no_leviCuspidal_subquotient_of_proper_induction_splitting`
   (module [CuspidalInductionExclusion](CuspidalInductionExclusion.md)) turns
   such a splitting of a proper inside-Levi induction into the statement that
   no nonzero actual subquotient of it is `IsLeviCuspidal`. Its proof uses
   actual first adjointness: a map from a cuspidal object into the induction
   vanishes, so the cuspidal component is zero. Its unimodularity premise for
   the restricted radical is the published
   `isUnimodularModulus_standardUnipotent_in_levi`.
3. `τ` is nonzero because it is irreducible (`IsSimpleModule.nontrivial`).
   Step 2 then contradicts the cuspidality of `τ`.

## Source and provenance

D. Renard, *Représentations des groupes réductifs p-adiques*, version of
9 July 2026, `renard-2026-representations-groupes-reductifs-padiques`
(SHA-256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`).
The Lemma VI.5.2 (printed p.173 / PDF p.179) says that no irreducible
subquotient of a proper parabolic induction `i^G_P(ρ)` is supercuspidal. Its
proof takes the supercuspidal part `π_sc` of `π = i^G_P(ρ)` in the
decomposition of Théorème VI.3.5 (printed pp.146–147 / PDF pp.152–153) and
observes `Hom_G(π_sc, π) = Hom_M(r^G_P(π_sc), ρ) = 0`, hence `π_sc = 0`. The
implemented proof follows exactly this route inside each actual standard Levi,
with Renard's supercuspidality read as the published proper-standard
`IsLeviCuspidal` predicate. The theorems are a derived composition of published
Library declarations, with the whole-category splitting kept as a hypothesis.
