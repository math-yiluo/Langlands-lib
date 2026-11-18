# Pullback of actual adic Hom systems

This internal construction is used for the finite étale descent step of the
adic Hom comparison. Let `φ : A →+* B` be a homomorphism of commutative rings,
let `I` be an ideal of `A`, and put `J = I.map φ`.

`quotientRingMap` is the induced map `A/I^(n+1) → B/J^(n+1)`.
`quotientSpecMap` is its contravariant affine scheme map. The structure-map and
transition identities are proved by reducing them to the corresponding ring
maps. `quotientOver` packages each map as a map of actual test schemes over
`Spec A`.

`isPullback_quotientSpecMap` states that these quotient maps give the Cartesian
square obtained by pulling `Spec B → Spec A` back to `Spec A/I^(n+1)`.
The proof uses the published pushout theorem for quotienting by an extended
ideal, with `Ideal.map_pow` identifying the extended ideal with `J^(n+1)`.
Flatness and surjectivity of the base map therefore pass to each quotient map.

`System.pull φ` pulls an actual compatible Hom system from `A` to `B`.
At level `n`, first evaluate the original homomorphism along `quotientOver`,
then apply `unflatten` to express the result as a homomorphism between the
base-changed groups. Its compatibility follows from the commuting quotient
transition square and `flatten_evaluate`.

`flatten_pull_hom` records that defining formula. `pull_restrict` proves that
pulling the restrictions of a global homomorphism gives the restrictions of
its base change. Finally, `pull_injective` assumes the affine base map is flat
and surjective, and proves that pulling systems is injective. At each level
the quotient map is flat, surjective and quasi-compact, so evaluation detects
equality of the original homomorphisms.

The provenance is internal: these definitions connect the Library's existing
`HomScheme.Adic.System`, actual Hom evaluation, and quotient-pullback theorem.
No completeness, noetherianity, or diagonalizability assumption is needed for
these adapters.
