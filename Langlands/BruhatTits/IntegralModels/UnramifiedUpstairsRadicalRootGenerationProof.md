# Full upstairs radical generation over maximal-unramified integers

`unramifiedUpstairsRadicalRootGeneration` proves exactly the existing
`UnramifiedUpstairsRadicalRootGenerationStatement.{u}` at arbitrary universe
`u`. One subgroup `H` is chosen before all nonempty subsets of a single
apartment facet, all characterized smooth integral models, and all
represented special-fibre unipotent radicals. The equality concerns the
entire subgroup of `G(inertiaFixedField F)` obtained by pulling the radical
point image back along the model's actual reduction map and mapping the
result along its actual generic integral-point map.

The proof first applies
`unramifiedUpstairsRadicalRootGeneration_of_singleton`. This reduction
preserves the common subgroup and the actual model and radical maps. It
uses constancy of the zero fixer and positive root fixers on nonempty
subsets of one facet; it requires no boundedness of the facet.

For the singleton formula, the proof chooses `H` using
`unramifiedZeroFixerCommonCentralizerRadicalExistence`. This supplies both
original bounds on `H` and identifies it with the intersection of every
actual upstairs radical preimage with the generic centralizer-point
image. The chosen singleton lies in its own facet, so this equality
applies to every supplied singleton model.

`unramifiedSingletonRadicalRootCentralizerGeneration` expresses that
model's full radical preimage as the join of its centralizer intersection
and all positive singleton root fixers. Rewriting the intersection as
`H` proves the singleton formula. The initial reduction then gives the
required equality on every nonempty subset of a single facet.

The supporting singleton theorem derives connected fibres and compatible
integral split-torus data from the model characterization. It combines
actual radical-preserving integral root generation with the positive-root
reduction criterion. The common-subgroup theorem discharges its
torus-centralizer radical-intersection input by the exact theorem
`torusCentralizerUnipotentRadical`. These are proved supporting results;
the final theorem has precisely the original proposition as its type.

This file is an internal composition of those results. The mathematical
source provenance and the distinction between the source's union
convention and the Library's positive root fixers are recorded in the
unchanged target Markdown, which derives the statement from
Kaletha–Prasad (2023), Corollary 8.4.12 and its supporting results, with
the registered corrections. The present proof uses the implemented
singleton and centralizer-intersection route described above.
