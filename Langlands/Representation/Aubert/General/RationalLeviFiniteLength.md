# Exactness and the alternating operator inside actual standard Levis

This is an internal specialization of the published exactness and alternating
operator constructions. It introduces no new literature assertion and proves
no Aubert identity.

The ambient group is the actual rational-point group of an affine group
scheme over a topological field, with the canonical `pointTopology`.
`J` is a finite subset of the actual `SimpleRoot i ν` subtype. Inside the
closed actual point subgroup `levi i ν J`, the parabolic, Levi and unipotent
subgroups are literally the `subgroupOf` restrictions indexed by
`leviIndex J I`, for `I : Finset J`. The decomposition is derived by
`isSemidirectDecomposition_in_levi` from the explicit
`StandardLeviIntersectionStatement`, connected reductivity, maximal splitness
and a generic cocharacter. This statement remains unproved here.

`standardLeviParabolicFiniteLength` applies
`ParabolicFiniteLength.of_preservesFiniteLength` inside that closed Levi.
Closedness gives its locally compact topology; the ambient nonarchimedean
and Hausdorff properties restrict to the subgroup. The ambient closedness
proofs for the standard parabolics and unipotents pull back along subtype
inclusion. The other inputs are continuity of the actual
`standardLeviProjection`, a compact-subgroup limit for each restricted
unipotent, and separate finite-length preservation for actual normalized
induction and normalized Jacquet restriction inside the Levi. The existing
induction and localization exactness proofs supply the two short-exactness
conjuncts. Neither exactness nor an Aubert equation is an opaque assumed field.

`rationalLeviAlternatingOperator` then specializes the existing
`leviAlternatingOperator` using precisely these derived decompositions and
finite-length/exactness witnesses. It acts on the exact finite-length smooth
Grothendieck group of `levi i ν J` at carrier universe `max (u + 1) v`.
Its index type is the finite subtype `J` and its coefficients are
`(-1)^|I|`, for `I : Finset J`; the imported `card_leviIndex` identifies this
with the cardinality of the corresponding ambient subset. There is no
additional rank sign. In particular `J = ∅` is permitted, as is an empty
ambient simple-root type. No ambient simple-root finiteness assumption is
needed to define the operator of a fixed finite `J`.

All topological and finite-length premises remain explicit. This unit does
not prove their realization, the shared intersection statement, endpoint
subgroup identities, conjugation comparisons, or any main identity. It
neither enlarges the permitted final external boundary nor restricts the
field to characteristic zero or the group to split or quasisplit cases.
Its proof route is the elementary actual-subgroup adapter followed by the
already implemented exactness theorems and existing signed sum.
