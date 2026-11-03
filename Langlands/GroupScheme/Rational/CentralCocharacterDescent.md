# Descent of central cocharacter orbit sums

Author: Worker 1264.

This is a derived prerequisite built from the published actual cocharacter
descent, base-change, transport, and split-component interfaces. It adds no
structural theorem as a hypothesis.

For a base morphism `b : S' → S` whose pullback functor on schemes is faithful,
`IsCentral.of_faithful_baseChange` reflects centrality of any group-scheme morphism.
For every test scheme, restriction, and pair of points, the proof applies
pullback to the desired commutation equality. The extended centrality supplies
that equality, preservation of multiplication identifies its two sides, and
faithfulness reflects it. Thus the result concerns the full all-test center.

`IsCentral.transportCocharacter` proves that the canonical transport along
an endomorphism of the base preserves a central cocharacter. Its proof uses
the published base-change stability, precomposition stability, and
postcomposition by the canonical descent isomorphism. Naturality with respect
to a specified morphism `t : T → M` then proves
`centralCocharacters_galois_stable`: if a cocharacter of `T_K` is central in
`M_K`, each Galois translate is central there.

Here `T` is an actual commutative group scheme over a field `k`, and `K/k`
is a field extension. The stability result requires no finiteness condition
on the extension. With a finite enumeration of its automorphisms,
`centralCocharacters_galoisOrbitSum_mem` follows because the central
cocharacters form the published integral submodule. With `K/k` finite Galois
and `T` affine, `centralCocharacters_descendedOrbitSum_mem` proves that the
published rational descended orbit sum is central in `M`. The exact
base-change formula identifies it with the central orbit sum over `K`;
faithfulness of field-extension pullback reflects centrality to `k`.

`CocharacterAveraging.descendedCentralOrbitSum` packages this actual
construction as a map from the subtype of central cocharacters over `K` to
the subtype of central cocharacters over `k`. Its underlying value is the
existing `descendedOrbitSum`. The accompanying base-change theorem recovers
exactly the integral Galois orbit sum, without division or a characteristic
restriction. Neither `T` nor `M` is assumed reductive or split, and the
construction does not require `T` to be a torus.

For affine `M` and a specified split component `a : A → M`,
`IsSplitComponent.exists_factor_descendedCentralOrbitSum` factors the
descended central cocharacter through `a` using its published universal
property for every map from a split torus. This applies to noninjective
cocharacters as well.

Finally, suppose `t` is monic on underlying schemes and `f : A → T`
satisfies `f ≫ t = a`. If an actual character `χ` of `T_K` restricts to zero
along the base change of `f`, then
`IsSplitComponent.latticePairing_centralOrbitSum_eq_zero` proves that `χ`
pairs to zero with the Galois orbit sum of each cocharacter central in
`M_K`. The integral range theorem for the specified split component factors
the descended sum through `f`. Extending that factorization makes its
composite with `χ` the zero morphism, whose integer exponent is zero.

These results prove central descent and the indicated pairing vanishing.
They do not assert base-change maximality of a chosen central torus, a
geometric Weyl action or positivity statement, or a Levi centralizer
description. The ambient maximal-split centralizer target remains separate.
