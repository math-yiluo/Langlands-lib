# Finite-extension norm maps and norm quotients

Worker 21 authored this construction module. The general algebraic constructors
retain independent universes for finite field extensions `L/K` and `M/L`.
The local constructors use actual `PadicField` objects, the specified
`TopologicalData` on each, and a compatible scalar tower over `Padic p`.
They impose no Galois, unramified or abelian-extension restriction.

`normUnits K L` is `Units.map (Algebra.norm K)`. Mathlib's algebra norm is
the determinant of multiplication on the finite-dimensional field extension.
`normSubgroup K L` is its actual image, `normToImage` restricts its codomain
to that image, and `NormQuotient K L` is the quotient of `Kˣ` by that
subgroup. `normQuotientProjection` is the actual quotient map.
No arbitrary subgroup stands in for a norm group.

For a finite tower, `normQuotientTowerProjection` sends the class of `a`
modulo `N_{M/K}(Mˣ)` to its class modulo `N_{L/K}(Lˣ)`.
`normQuotientTowerNorm` sends the class of `b` in
`Lˣ/N_{M/L}(Mˣ)` to the class of `N_{L/K}(b)` in
`Kˣ/N_{M/K}(Mˣ)`. Their intrinsic containment certificates use Mathlib's
proved norm transitivity. They do not assume a class field theory diagram.

`localInclusion T S` is the map on multiplicative groups induced by the
specified field inclusion. Its continuity follows from linearity over
`Padic p` and the supplied module topologies.
`localNorm T S` is the actual norm with a proved continuity certificate.
Finite dimensionality of the upper field over the lower is inherited
from its finite dimension over `Padic p`. Choose a finite basis over the
lower field; the multiplication-matrix map is linear over the lower field,
hence over `Padic p` after restriction of scalars. The module-topology
certificate gives continuity of this map, and continuity of determinant
then gives continuity of the norm. Applying `Continuous.units_map`
gives the asserted map of multiplicative topological groups.
This argument requires no unproved comparison of normalized absolute
values, ramification indices or field norms.

`localNormSubgroup` and `LocalNormQuotient` specialize the general image
and quotient to these actual local fields. The subgroup is algebraic
data and does not depend on a choice of the supplied topology.
`localNormQuotientProjection T` uses the genuine quotient topology of the
units topology induced by `T.topology`. No discreteness, compactness,
finite index or norm-subgroup openness is asserted or assumed.
`localNormQuotientTowerProjection` and `localNormQuotientTowerNorm`
provide the continuous versions of the two tower maps. Their continuity
follows from the quotient-topology criterion, respectively applied to the
quotient projection and to its composite with the proved continuous local
norm. No topology on the top field is needed for these quotient-map
certificates: the norm images are algebraic and the two quotient topologies
are those of the middle and lower fields.

## Sources and scope

Jean-Pierre Serre, *Local Fields*, English translation, GTM 67 (1979),
Chapter I, Section 5, Proposition 14 and its proof, printed page 17
(retained PDF page 25), identifies the field norm with the determinant of
multiplication. Chapter II, Section 2, Proposition 3, printed pages 28-29
(PDF pages 36-37), identifies finite-extension topology with the
finite-dimensional module topology. Chapter V studies these actual norms
and their unit images; none of its additional image formulas are assumptions
of this construction.

Source ID `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`,
file `C:/Central-Library/Serre--Local Fields--1979.pdf`.
The quotient maps and determinant-continuity certificate are derived
interfaces, with the exact formulas above. This is not a construction of
an Artin map or a reciprocity isomorphism.

## Dependencies

The project import is `Langlands.LocalField.Definitions`, artifact
`ac4cb7d5-5dd1-44b6-9d56-f0ec6c70bce0`, version 1.
Environment `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1, pins
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
This module is independent of the pending local unit-filtration contribution.

The principal Mathlib declarations are `Algebra.norm`,
`Algebra.norm_norm`, `Algebra.norm_eq_matrix_det`, `Algebra.leftMulMatrix`,
`FiniteDimensional.right`, `IsModuleTopology.continuous_of_linearMap`,
`Continuous.matrix_det`, `Units.map`, `Continuous.units_map`,
`QuotientGroup.mk'`, and `QuotientGroup.map`.

## Topic-hierarchy migration

Worker 63 relocated this pair from `Langlands.LocalClassField.Norms` to
`Langlands.ClassFieldTheory.Local.Norms` at Library base
`c139df9ce67284be1bc963c2de5fbebd90214dda`. Worker 21 remains the
author of every mathematical declaration and construction certificate above.
Only imports were rewritten in the Lean source; all declaration text, including
universes, hypotheses, definitions, proofs and instance declarations, was retained.
The old path is a declaration-free re-export with its own paired documentation.

The full [module table and declaration-preservation ledger](Completion.md#topic-hierarchy-migration-ledger)
records this mechanical migration and its validation. Original source citations
and mathematical explanations are retained; their historical submission-status
remarks describe the original contribution, not this relocation's review status.
