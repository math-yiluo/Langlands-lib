# Refining selections over original-chart domain covers

This internal construction assembles local original-chart selections into a
global refining selection. It is a prerequisite for comparing full morphisms
after source refinement on a quasinet cover.

The coefficient field is a complete nonarchimedean normed field. The field,
ambient space, original chart index, and cover index have independent universes
`u`, `v`, `w`, and `z`. The atlas is an `IndexedAffinoidAtlas`; each covering
member is an actual `OriginalChartDomain`, with its induced subspace topology
and its atlas of contained original charts.

## Provenance and scope

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
Definition 1.3.1 on printed p.23 (PDF p.20) gives the finite relative
neighborhood convention for domains. Proposition 1.3.2 on printed p.24
(PDF p.21) motivates descent over such domain coverings, and the G-topology
paragraph on printed p.25 (PDF p.22) uses quasinet covering families.
The registered source is `berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.

The selection construction here is derived internal infrastructure, rather
than a separately asserted theorem of that source. It uses only the original
atlas net axioms, actual subspace atlases, and finite relative local
refinements. It requires no saturation hypothesis. It does not prove
Proposition 1.3.2, gluing of quotient morphisms, or identification of the
original-chart domain class with the full analytic domains of a maximal
finite-gluing atlas.

## Construction

Let `D k` be a family of original-chart domains, and let `R k` be a
downward-closed, locally refining selection in the subspace atlas on `D k`.
Assume the actual family of subsets `D k` locally refines the whole space:
at each point, finitely many members contain that point and their union
is a neighborhood.

`domainCoverSelectionPredicate D R i` holds exactly when some `D k`
contains the entire range of original chart `i` and the corresponding
subspace chart is selected by `R k`. Downward closure follows by retaining
that same `k`, composing range inclusions, and using the downward closure
of `R k`.

`domainCoverSelectionPredicate_locallyRefines` proves that these ambient
selected chart ranges locally refine every `D k`. The selected subspace
charts form a quasinet by the existing selection theorem. Taking ambient
images and restricting back recovers the same family exactly, so the
subspace quasinet gives finite neighborhoods relative to `D k`. Each
ambient image is literally the range of the underlying original chart,
with precisely the defining selection witness.

Composing this refinement with the domain cover proves
`domainCoverSelectionPredicate_isQuasinet`. Finite relative neighborhoods
of the whole space are ordinary neighborhoods.

The reusable theorem
`IsDownwardClosedSelection.isLocallyRefining_of_isQuasinet` upgrades a
downward-closed quasinet of original charts to local refinement inside
every original chart. It intersects global finite neighborhoods with
that chart and then uses the original net intersection axiom to refine
each resulting intersection by original charts. Those charts lie inside
a selected chart, so downward closure keeps them selected. Composition
of the finite relative refinements gives the required witnesses.

`coverRefiningSelection D R hD` bundles the constructed predicate and
these two proofs. `mem_coverRefiningSelection` gives its exact existential
membership formula, so each selected global chart retains a covering
domain and its local selection witness. `coverRefiningSelection_mono`
proves monotonicity when each local selection is enlarged. Empty spaces
and empty covering families are permitted whenever the stated cover
condition holds.
