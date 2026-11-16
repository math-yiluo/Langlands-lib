# Closed Chevalley subgroups in every field fibre

Fix integral Chevalley data, a Dedekind domain with a specified fraction field,
and one actual generic Chevalley group. This internal construction embeds every
supplied field Chevalley group in the corresponding field fibre of that one
fixed integral schematic closure. The field-valued point is any ring
homomorphism from the domain to the field; no characteristic restriction is
imposed.

The matrix inclusion of the fibre is the base change of the integral closed
inclusion followed by the canonical general-linear comparison isomorphism.
It is therefore closed. Define the fibre torus and root homomorphisms by
precomposing the base changes of the integral homomorphisms with the inverse
diagonalizable and additive comparison isomorphisms. Their matrix composites
are exactly the original field torus and root maps, by the arbitrary-ring
base-change identities in `TorusClosure` and `RootClosure`.

Consequently this closed matrix subgroup contains the torus and every root
map as subgroup functors on all test schemes. The generator factorization in
`FieldSubgroup` gives the actual closed embedding of the supplied field
Chevalley group, retaining its original matrix representation. Cancellation
through the fibre matrix inclusion identifies the torus and every root map
under that embedding.

This is a consequence of the named internal constructions. It proves only
containment of the field Chevalley group in the integral fibre. Reverse
containment, equality of fibres, smoothness and reductivity of the integral
model, and the common full fibre root datum remain further obligations.
