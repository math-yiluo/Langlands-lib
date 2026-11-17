# Semisimplicity characterized by the solvable radical

This module proves the unchanged published proposition
`Langlands.GroupScheme.SemisimpleRadicalCharacterizationStatement.{u}` by
`Langlands.GroupScheme.semisimpleRadicalCharacterization.{u}`. It works in every
universe, over every field, for every smooth connected affine group scheme.
The second equivalence assumes that the group is connected reductive, exactly
as in the target.

## Implemented proof

Two helper theorems record the steps used in the proof.

`HasTrivialSolvableRadical.hasTrivialUnipotentRadical` applies the solvable-radical
condition to each smooth connected normal unipotent closed subgroup. Such a
subgroup is affine, since the ambient group is affine. The published theorem
`isSolvable_points_of_isUnipotent` gives solvability of its points over the
algebraic closure, and `isSolvableGroupScheme_of_isSolvable_points` gives the
precise solvability predicate tested by `HasTrivialSolvableRadical`.

`IsSemisimple.hasTrivialSolvableRadical` first uses
`reductiveGeometricSolvableRadicalExists` to choose a represented geometric
solvable radical `r : R ⟶ G`. The published theorem
`IsGeometricSolvableRadical.isTorus_and_isCentral_of_structural`, applied to the
proved `algClosedReductiveNormalSolvableTorus`, makes `r` central. The group `R`
is smooth, connected and affine. Therefore
`IsCentral.eq_one_of_hasFiniteCenter` makes its map to the finite full centre
trivial. `SubgroupFunctor.range_eq_bot_iff_hom_eq_one` gives `range r = ⊥`, and
the greatestness of the represented radical kills every subgroup in the
solvable-radical condition.

For the geometric equivalence, a semisimple group remains semisimple over the
chosen algebraic closure: connected reductivity is supplied by
`IsConnectedReductive.baseChange_toAlgebraicClosure`, and finiteness of its full
centre by `HasFiniteCenter.baseChange`. The preceding helper then gives trivial
solvable radical there. Conversely, trivial solvable radical over the algebraic
closure implies trivial unipotent radical by the first helper, giving connected
reductivity over the original field. The published algebraically closed theorem
`HasTrivialSolvableRadical.hasFiniteCenter` gives a finite full centre over the
closure; `HasFiniteCenter.of_fieldExtension` descends it to the original field.
These are the two fields of `IsSemisimple`.

For the rational equivalence under connected reductivity, the forward direction
is the second helper. In the reverse direction, choose a represented geometric
solvable radical. The rational hypothesis kills its image over the ground field.
`SubgroupFunctor.range_baseChangeHom` and `SubgroupFunctor.bot_baseChange` then
kill the image of its base change. Since this base change is itself the solvable
radical, its greatestness gives the geometric radical condition. The first
equivalence now supplies semisimplicity.

All triviality assertions concern subgroup functors on every test scheme. The
finite centre is the full scheme-theoretic centre, including nilpotents. No
perfectness, characteristic, splitting or extra subgroup hypotheses are added.

## Provenance and dependency scope

This proof is derived from the published Library results listed above. The
source correspondence of its target is documented in
[SemisimpleRadicalCharacterizationStatement](SemisimpleRadicalCharacterizationStatement.md).
Its mathematical route follows J. S. Milne, *Algebraic Groups* (2017), Definition
6.44 (printed p.135) and Proposition 19.10 (printed p.400): for reductive groups
the radical commutes with field extension and is a central torus; finiteness of
the centre kills it. The reverse geometric direction also uses the solvability
of unipotent groups from Proposition 14.21 (printed p.284). These structural
inputs are imported as proved Library results rather than assumed.

The original Proposition 19.10 and its proof on printed p.400 were checked in
the registered source `milne-2017-algebraic-groups`. The registered official
errata snapshot `milne-2017-algebraic-groups-errata-2026-11-02` has no correction
to Definition 6.44 or Proposition 19.10. The auxiliary lemmas are internal
consequences of the imported radical, centrality, finite-centre and unipotent
solvability results; they introduce no new definitions or assumptions.
