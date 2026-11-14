# Big-cell gluing from arbitrary algebra points

This internal consequence of the Library's `CellGluing` removes reducedness
from the gluing step when comparisons are supplied on all commutative
algebras. It does not construct those comparisons.

Let `R` be any commutative ring, and let `G` and `H` be reductive group
schemes over `Spec R`. Give them maps from the same coordinate split torus
and families of additive-group homomorphisms indexed by the same type.
Suppose the resulting big-cell maps, with the same two root enumerations,
are open immersions. For every commutative `R`-algebra `A`, assume there is
an isomorphism between the point groups over `Spec A` that matches the
torus points and each chosen additive-group parametrization. Then there is
an actual group-scheme isomorphism `G ≅ H` agreeing with these coordinates
on the common big cell.

`LocalSplitAlgebraCellIsomorphismStatement` expresses exactly this
criterion at arbitrary universe `u`, and `localSplitAlgebraCellIsomorphism`
proves it. The maps from the additive group need no separate root-subgroup
specification in this criterion: their use is through the given open
big-cell maps and the supplied comparison identities. The comparison
isomorphisms may be chosen separately for every algebra; no naturality
assumption is imposed.

There is no reducedness, locality, noetherian, henselian or characteristic
assumption. Tests include algebras with nilpotents.

The proof first establishes `CellGluing.cellCompatible_of_ringPoints`.
A multiplication relation between cell points over any scheme restricts
to every member of its affine open cover. The assumed relation over the
spectrum of that chart's ring then gives equality on the chart. Equality
of morphisms on the open cover gives the required global relation. This
uses neither reducedness of the scheme nor separatedness of the target.

`LocalSplitCell.exists_iso_of_ringPoints` applies this fact in both
directions. A comparison isomorphism preserving the torus and each
additive-group map preserves each ordered product in the big-cell map,
so it carries a cell multiplication relation to the corresponding
relation in the other group. Its inverse gives the reverse implication.
Reductivity supplies smoothness and geometrically irreducible fibres.
The existing `CellGluing.exists_iso_of_cellCompatible` therefore glues the
group-scheme isomorphism with the asserted equality on the cell.

`LocalSplitCell.exists_iso_of_algebraPoints` passes from an arbitrary
structure map `Spec A → Spec R` to the algebra structure determined by its
ring homomorphism, and transports the point comparisons along the
identity isomorphism with the canonical algebra test object.
The existing name `LocalSplitCell.fieldPoint R A` is used for that object;
its definition already permits arbitrary commutative algebras.

The provenance is derived: the argument uses open-cover equality,
`LocalSplitCell.cellRelation_of_map` and the published open-cell
gluing theorem. It is independent of the unrestricted local split
Isomorphism Theorem. Producing the arbitrary-algebra comparisons remains
an additional obligation; field comparisons alone do not supply this
input over a nonreduced ring.
