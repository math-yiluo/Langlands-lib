# Fixed-vector visibility of Bernstein classes from support uniqueness and the standard-representative criterion

Author: Worker 733, Task 6639 (`97df9594-40e0-45d8-8f8c-0e7562c6b4de`).

This module proves the Library predicate
`bernsteinFixedVectorVisibility i ν family K` at a level `K` with Iwahori
decompositions, from two explicit hypotheses. Both theorems are conditional.
They prove neither hypothesis, and they do not prove visibility
unconditionally. No new definitions are introduced.

## Setting

`F` is a nonarchimedean local field and `G` a group scheme over `F` with
`IsAffineHom` and `LocallyOfFiniteType` structure maps. `G(F)` has the point
topology and is assumed locally compact and nonarchimedean. `i` is a torus,
`ν` a cocharacter, `family : BernsteinStandardFamily i ν`, and `K` an open
subgroup of `G(F)`. Both theorems take the following hypotheses:

- `hstd`: every `J ⊆ simpleRelativeRoots i ν` has a standard cocharacter;
- `hK`: `K` is compact;
- `hIwahori`: `K` has an Iwahori decomposition
  (`HasIwahoriIntersectionDecomposition`) along every standard parabolic
  `M_J N_J`, `J ⊆ simpleRelativeRoots i ν`;
- `huniq`: the Library's
  `BernsteinInertialSupportUniquenessStatement.{uF, uV} i ν family`
  (an irreducible has at most one inertial support);
- `hcrit`: the direction (⇒) of the standard-representative criterion at `K`.
  For every cuspidal datum `a` of the family (carrier universe `max uF uV`):
  if some irreducible with inertial support `[a]` has a nonzero `K`-fixed
  vector, then the transported cuspidal representation
  `bernsteinLiteralLeviRep i ν a.roots a.representation` has a nonzero
  `K ∩ M_a`-fixed vector. Here `M_a = levi i ν a.roots`. This is literally the
  forward implication of one instance of the published
  `StandardRepresentativeFixedVectorCriterionStatement`.

## Statements

- `nontrivial_fixedVectors_of_sameInertialSupport`: let `π` and `τ` be smooth
  representations at carrier universe `max uF uV`, both with inertial support
  `s` (`IsBernsteinInertialSupport`). If `π` has a nonzero `K`-fixed vector,
  so does `τ`.
- `bernsteinFixedVectorVisibility_of_uniqueness_of_necessity`: under the same
  hypotheses, `bernsteinFixedVectorVisibility.{uF, uV} i ν family K` holds.
  This is the two-sided statement, with universes `uF` and `uV` independent.

## Proof

For `nontrivial_fixedVectors_of_sameInertialSupport`, the representation `τ`
is irreducible, as part of having an inertial support. The published
`exists_bernsteinCuspidalDatum_jacquet_quotient_induction_embedding` gives a
cuspidal datum `c` of the family with two properties:

- `bernsteinLiteralLeviRep i ν c.roots c.representation` is a quotient of the
  normalized Jacquet module of `τ` along `P_{c.roots}`;
- `τ` embeds in the induction of `c`.

The embedding makes `c` a cuspidal support of `τ`
(`IsBernsteinCuspidalSupport.inertial`). So `[c]` is an inertial support of
`τ`, and `huniq` gives `[c] = s`. Now `π` has inertial support `[c]` and a
nonzero `K`-fixed vector. By `hcrit`, the transported cuspidal representation
of `c` has a nonzero `K ∩ M_c`-fixed vector. The group `K ∩ M_c` is compact
because `M_c` is closed (`family.closedLevi`). The published
`SmoothRep.nontrivial_fixedVectors_of_isSubquotient` therefore lifts the
fixed vector along the quotient map: the normalized Jacquet module of `τ` has
a nonzero `K ∩ M_c`-fixed vector. Finally
`nontrivial_fixedVectors_of_standardNormalizedJacquet` (module
`IwahoriJacquetNonvanishing`) gives a nonzero `K`-fixed vector of `τ`. It uses
`hstd` and `hIwahori` at `J = c.roots`, and needs no admissibility.

The second theorem applies the first in both directions.

## Source and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, VI.10.6: the Proposition (i) and the proof of the
Corollary (printed pp.214–215 / PDF pp.220–221), with the preceding
Theorem's proof (printed pp.213–214 / PDF pp.219–220). Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The provenance is derived. In the source, `B(G)_K` is well defined because
`K`-fixed vectors are detected on the cuspidal representation of the inertial
class: that is the criterion (Corollary, first claim). The source passes
from the Levi back to `G` through Jacquet's lemma for `K` with an Iwahori
decomposition. Here that step is the admissibility-free nonvanishing lemma of
`IwahoriJacquetNonvanishing`, and only the necessity direction of the
criterion is used. The support uniqueness, which the source takes from VI.5.4
and VI.7.2, is the explicit hypothesis `huniq`.
