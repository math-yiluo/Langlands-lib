# Genuine restricted-product action

This module constructs a representation of Mathlib's actual
cofinite restricted product of the local groups on the actual algebraic
restricted tensor product. The coefficient field, index, groups and local
vector spaces have independent universes. Local carriers may be infinite
dimensional.

Each local subgroup fixes the prescribed reference vector outside the finite
exceptional set. Membership in the restricted product therefore makes the
component operators preserve reference vectors at all but finitely many
indices. The previously constructed induced linear map supplies the action.
Its identity and multiplication laws follow from the identity and composition
laws of induced maps. The elementary formula is proved both after enlargement
and on any stage outside which the group element belongs to the reference
subgroups. Component intertwiners preserving references almost everywhere
induce an intertwiner of these representations. `productRepresentation`
specializes to reference vectors required to be nonzero only outside the
exceptional set.

The original construction is Flath (1979), section 2, printed pages 180–181,
especially Example 2 on page 181 (one-based PDF page 177). Registered original:
`flath-1979-tensor-products`, Corvallis Part I, SHA-256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
Smoothness is proved in the associated `Smooth` module.
This module does not assert factorization, admissibility, or one-dimensional
fixed-vector spaces. The raw group action needs no topology or compactness.

`RestrictedGroup` is only an abbreviation for Mathlib's `RestrictedProduct`
with the cofinite filter; it is not a substitute abstract group. Its elements
are genuine families of group elements lying in the chosen subgroups
cofinitely. `action_preserves` combines this condition with the finite
exceptional set and the local fixed-vector assumptions. `representation`
is a genuine `Representation`, with linear operators supplied by `map`
and both monoid laws proved.

`representation_pure` describes the action after enlargement by a finite
bound. `representation_pure_of_mem` keeps the original tensor stage when
the group element is in the reference subgroups everywhere outside it.
`map_intertwines` proves equality of the two composite linear maps by the
composition law for restricted tensor maps and the local intertwiner
equalities. Source and target exceptional sets may differ. All component
maps need only preserve reference vectors cofinitely.
