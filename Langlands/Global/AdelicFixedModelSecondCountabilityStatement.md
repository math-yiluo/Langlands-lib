# Second countability of actual full-adele model points

`AdelicFixedModelSecondCountabilityStatement` asserts second countability
of the actual full-adele point space of every finite-type arithmetic
model, with exactly the topology final from its actual arithmetic stages.
It is a derived specialization of the direct-limit and countable-base
discussion in Section 4 of Brian Conrad, *Weil and Grothendieck approaches
to adelic points* (December 31, 2011), printed page 9.

The two clauses quantify actual schemes over the function-field and
number-field outside-`S` integer rings. Local finite type and
quasi-compactness of the structure morphism express finite type.
`CurvePlaceFixedModelAdelePoints` and `NumberFieldFixedModelAdelePoints`
are relative scheme morphisms from the spectra of the actual full adele
rings, with the original integer-base actions.
`curvePlaceFixedModelAdelePointTopology` and
`numberFieldFixedModelAdelePointTopology` are final from fixed-base
arithmetic stages indexed by all finite supersets of `S`. Each stage
retains the topology obtained from the actual local-model product. The
target assumes no comparison bijection, open map or topological property.

The function-field clause retains finite constants, the original
`k`-algebra structure, a compatible rational-function scalar tower and
`FunctionField k F`. The number-field clause includes every infinite
completion. Both permit empty `S` and nonaffine models. The statement is
uniform in an arbitrary common universe `u`.

The derivation has two parts. First, actual place sets are countable, so
the finite supersets of `S` form a countable index set. Each local-model
point space is second countable by the finite-coordinate and finite-affine
cover argument derived from Propositions 2.1 and 3.1. Countable products
and induced topologies then give second countability of the arithmetic
stage spaces, including those transported to the fixed initial base.
Second, the integer base is Noetherian, so local finite type implies local
finite presentation. The actual finite-presentation point comparison
shows that the images of all stages cover every full-adele model point.
Stage transitions are continuous and open. Their final-topology maps
are therefore continuous and open. Images of countable bases from
countably many covering stages form a countable basis of the full space.

This argument also proves the stated nonseparated extension: Section 4
gives a countable base together with local compactness and Hausdorffness
for separated generic fibres, whereas the countable-basis argument just
described uses openness and coverage, without injectivity or
separatedness. Empty `S` is retained because the actual integer bases
remain Noetherian and the same countable-stage argument applies.

This target concerns the full-adele points of a fixed arithmetic model.
Generic-fibre identification, existence of spreads and independence of
the chosen spread remain separate comparison results. This file defines
a proposition; it supplies no proof or claim of whole-paper completion.

Source: registered literature
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`,
printed pp.2 and 4, Propositions 2.1 and 3.1, and printed page 9,
Section 4's opening direct-limit and countable-base argument. The
fixed-model formulation and the nonseparated and empty-`S` extensions
are derived as explained above.
