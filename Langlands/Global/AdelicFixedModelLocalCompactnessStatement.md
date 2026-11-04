# Local compactness of full-adele model points

`AdelicFixedModelLocalCompactnessStatement` concerns actual full-adele points
of a finite-type arithmetic model, with the final topology from its actual
arithmetic stages. It is a derived specialization of the direct-limit
argument at the start of Section 4 of Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), printed page 9, using
Corollary 3.7 on the same page.

The model `X` is an actual scheme over the outside-`S` integer ring.
`LocallyOfFiniteType X.hom` and `QuasiCompact X.hom` express finite type.
`CurvePlaceFixedModelAdelePoints` and `NumberFieldFixedModelAdelePoints`
are actual relative scheme morphisms from the spectrum of the full adele
ring, with the original integer-base action. Their topologies are exactly
`curvePlaceFixedModelAdelePointTopology` and
`numberFieldFixedModelAdelePointTopology`. These are final from the
fixed-base arithmetic stage point spaces indexed by finite supersets of
`S`; each stage has the original product-induced arithmetic-model topology.
No point bijection, openness, compactness or topological property is a
premise of this statement.

The conclusion is local compactness for every such model, with Hausdorffness
when the structure morphism is separated. The statement retains nonaffine
and nonseparated models, with separatedness required only for Hausdorffness.
It is uniform in any common universe `u`.

The function-field clause retains the original `k`-algebra structure of
`F`, finite constants `k`, a compatible rational-function scalar tower and
`FunctionField k F`. There is no separability premise. Finite constants are
essential to the arithmetic compactness input; no assertion is made over
infinite constant fields. The number-field clause covers every number
field and retains all infinite completions in every stage and in the full
adele ring.

This target states a property of the fixed arithmetic model on the full
adele ring. It does not itself identify these points with points of the
generic fibre or assert independence of the chosen arithmetic model.
Those use separate comparison and descent results.

Two extensions beyond the source's formulation are explicit. First,
Section 4 asserts local compactness and Hausdorffness together for
separated generic fibres. Here local compactness alone is also asserted
without separatedness: the actual arithmetic transitions are continuous
and open, the stage spaces are locally compact by Corollary 3.7, and the
finite-presentation point comparison covers the full point space by their
images. A compact neighbourhood in a stage maps to a compact
neighbourhood under a continuous open stage map. This argument uses no
Hausdorff assumption. Separatedness supplies injective transitions and
Hausdorff stages for the Hausdorff conclusion.

Second, the finite initial set `S` may be empty. All infinite number-field
factors are already present independently of `S`. The curve empty level
has only integral factors. The integer bases remain Noetherian, so the
finite-type point comparison and the same direct-limit argument still
apply. This extension does not assume a nonempty set of places.

This file defines a proposition to be proved. It does not supply its proof,
second countability, or the remaining topological assertions of Section 4.

Source: registered literature `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`,
printed page 9, Corollary 3.7 and Section 4's opening direct-limit argument.
The fixed-model formulation and the two extensions above are derived as
explained here.
