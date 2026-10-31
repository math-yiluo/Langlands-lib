# Common original-chart subatlases

This module constructs common subatlases for downward-closed, locally refining
selections of the original charts of a supplied `IndexedAffinoidAtlas`.
It reuses [AtlasSubatlas.md](AtlasSubatlas.md) and the derived composition
calculus in [AtlasTopology/RefinementComposition.md](AtlasTopology/RefinementComposition.md).

The original conventions are Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), §1.1, printed pp.13–14
(PDF pp.10–11), and Definition 1.2.3 and Remark 1.2.4(i), printed p.16
(PDF p.13), registered as `berkovich-1993-etale-cohomology`.
The retained original is
`Berkovich--Etale cohomology for non-Archimedean analytic spaces--1993.pdf`,
SHA-256 `06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
These passages were reread for this unit; no source-specific project errata
file was found. The selection calculus here is derived infrastructure from
the net and atlas definitions, not a numbered source theorem.

`IsDownwardClosedSelection P` says that an original chart is selected
whenever its range is contained in the range of a selected original chart.
This quantifies over original chart indices. The monotonicity lemmas show
that enlarging a selection enlarges its chart family and retains local
refinement. Selecting every chart is locally refining and downward closed.
Conjunction preserves downward closure.

`IsLocallyRefiningSelection.and` assumes local refinement for `P` and `Q`
and downward closure for `P`. For a selected `P`-chart, take its finite
relative local refinement through `Q`. Every witness chart is contained
in that `P`-chart, so downward closure also selects it in `P`. Thus these
are witnesses for `P ∧ Q` refining the `P`-family. Composing this refinement
with the given refinement of the original atlas through `P` proves local
refinement for the conjunction. Neither the output net nor an output atlas
is an input to this proof.

`RefiningSelection` bundles a set of chart indices with downward closure
and finite relative local refinement witnesses. Its order is inclusion.
The proved conjunction result constructs its infimum as literal intersection;
its top selects every original chart. The `SemilatticeInf` and `OrderTop`
instances provide the usual finite meet calculus for such selections.
`mem_inf` and `mem_top` record the membership formulas.

For a presentation `A`, `refiningSubpresentation` applies the published
`subpresentation` construction. It retains the actual space, selected
presented positive-polyradius algebras, embeddings, bounded restrictions,
and full affinoid-domain universal properties, with the selected net proved
by the imported construction. `refiningSubatlasMap` uses the published
`subatlasMap` for an inclusion of selections. The full chosen-arrow identity
and composition laws give `refiningSubatlasFunctor` from the order category
of refining selections to the category of chosen atlas maps.

`commonSubpresentation P Q` realizes `P ⊓ Q`. Its indices are precisely
original indices selected by both predicates. `commonSubatlasToLeft` and
`commonSubatlasToRight` are canonical chosen maps to the two selected
presentations. Each has the identity continuous map, the corresponding
subtype inclusion on indices, and actual bounded identities on chart
algebras, as the point and pullback formulas record. The
`commonSubatlas_diamond` equality follows from the published factorization
law for nested selections: both composites to `A` are the same inclusion
of the common subatlas. This is equality of full chosen arrows, including
the dependent bounded algebra maps.

The field, space, and chart-index universes remain independent `u`, `v`,
and `w`. This construction concerns selections on one supplied actual
atlas. Downward closure and local refinement are substantive hypotheses;
the intersection of arbitrary locally refining selections is not asserted
to refine the atlas. The module does not construct new affinoid-domain
algebras, extended atlases, localization of chosen maps, structure sheaves,
or analytic sites. No categorical product or pullback property of the
common presentation in the full chosen-map category is claimed.
