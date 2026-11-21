# Finite compact refinements for the compact-probe quasi-étale topology

Author: Worker 21.

`Langlands.Analytic.SaturatedAtlasPresentation.CompactProbeQuasiEtaleCompactRefinementsStatement K`
is a proposition for a complete ultrametric normed field `K`. Let `X` be in
`LocalizedCategory.{u, v, v} (K := K)`, let `U` be in `QuasiEtaleSite X` with
`IsCompactSpace U.left` (compact and Hausdorff), and let `S` be a sieve on
`U` that covers for [`compactProbeQuasiEtaleTopology X`](QuasiEtaleCompactProbeTopology.md).
The conclusion asks for `n : ℕ`, `V : Fin n → QuasiEtaleSite X`, and arrows
`f i : V i ⟶ U` such that:

- each `(V i).left` is compact Hausdorff;
- each `f i` belongs to `S`;
- the sieve `Sieve.ofArrows V f` they generate still covers for
  `compactProbeQuasiEtaleTopology X`.

There is no Hausdorff hypothesis on `X`. This is the replacement for
`QuasiEtaleCompactRefinementsStatement`, which refers to a different, legacy
topology on the same site category. This pair neither changes that
proposition nor restates any downstream condition.

## Provenance and scope

Berkovich, *Vanishing cycles for formal schemes*, Invent. Math. 115 (1994),
§3, printed p. 544 (PDF p. 6), describes quasi-étale covering families using
neighbourhoods that are finite unions of affinoid-domain images. Compact
refinement is motivated by selecting finitely many such neighbourhoods on a
compact object. The statement here is derived: both covering predicates in
it use the direct compact-probe test, not a generated precoverage.

The identity probe of `U` extracts a finite jointly surjective family in `S`
by `containsFiniteCompactSurjection_of_mem_compactProbeQuasiEtaleTopology`.
Showing that this family generates a covering sieve is a further geometric
step. One route pulls its arrows back along any compact Hausdorff probe
using compact binary site pullbacks over `U` that lift pairs of points with
matching images. For background on analytic fibre products and their map
to the topological fibre product, see Berkovich, *Étale cohomology for
non-Archimedean analytic spaces*, Publ. Math. IHÉS 78 (1993), §1.4,
Proposition 1.4.1, printed pp. 29–30 (PDF pp. 26–27). No pullback theorem is
assumed in the proposition. This module defines the target; it does not
prove the refinement result.
