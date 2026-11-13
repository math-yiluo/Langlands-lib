# Reductive Kottwitz existence, independence and descent

These four Prop-valued declarations state the construction and properties in Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), §11.5 and Lemma 11.5.1, printed pp. 429–430 (PDF pp. 460–461). The z-extension existence input is Construction 11.4.1, printed p. 428 (PDF p. 459). The November 2024 corrections leave these items unchanged. The declarations are statements awaiting proofs.

All local fields are allowed, in equal and mixed characteristic, without splitting, ramification, rank or residue-characteristic restrictions. The auxiliary field `k`, equipped with compatible maps to `K = UnramifiedClosure F` and `E = SeparableClosure F`, records the field of definition of the original group scheme. The statement hypotheses require that `E` be a separable closure of `k` and that `K/k` be normal; in particular they include the intended choices `k = F` and `k = K`. No Kottwitz map, z-extension, commuting square, surjectivity or kernel identity is assumed.

## Simply connected derived group

`SimplyConnectedDerivedKottwitzStatement` asserts for every connected reductive group whose derived subgroup is simply connected:

- There is exactly one homomorphism satisfying every actual cocenter square.
- The selected `simplyConnectedDerivedKottwitz` satisfies that property and is surjective on `K`-points.
- For every actual cocenter, the map `π₁(G)_I → X_*(D)_I` used in the square is bijective.
- For each individual cocenter, a homomorphism satisfies that one square if and only if it equals the selected map.

This is KP's first construction in §11.5, including the induced isomorphism on fundamental groups and its inertia version. Unique characterization by any cocenter makes its independence explicit. The cocenter is an actual full fppf quotient, not supplied abstract point data; its nonemptiness is proved in the definition module.

## Z-extensions

`ReductiveKottwitzExistenceStatement` asserts, for every connected reductive group, that an actual z-extension exists, that there is exactly one homomorphism satisfying all z-extension squares, that the selected `reductiveKottwitz` satisfies them, and that it is surjective on `K`-points. It also agrees with `simplyConnectedDerivedKottwitz` whenever the latter applies.

For every individual z-extension, the statement asserts surjectivity of `H(K) → G(K)` and of `π₁(H)_I → π₁(G)_I`. A homomorphism satisfies its square if and only if it equals the selected reductive map. This is the explicit uniqueness and independence content of Lemma 11.5.1. The point and inertia surjectivity assertions are the inputs stated immediately before the lemma, with inertia surjectivity following by right exactness of coinvariants. Z-extension existence is also a separate general-field Library target; it is a conclusion here rather than an extra hypothesis.

## Functoriality and the torus construction

`ReductiveKottwitzFunctorialityStatement` gives the commuting square for every actual morphism `H → G` of connected reductive groups. The horizontal map on points is coefficient evaluation of that morphism, and the other horizontal map is its induced inertia map. The statement also compares the reductive map on every torus to the original torus Kottwitz map using the canonical inertia comparison. This makes the extension of the torus construction explicit. This compatibility is the torus case of the cocenter construction and the functoriality of Lemma 11.5.1.

## Galois descent

`ReductiveKottwitzDescentStatement` asserts equivariance for every actual element of `Gal(K/k)` in the preceding compatible tower. For an `F`-group it additionally states `ReductiveKottwitzEquivariant`, unique existence of an invariant-valued restriction on actual rational points, and that `reductiveKottwitzRational` is this restriction. These are the last assertion of Lemma 11.5.1 and the definition following its proof. They do not assert surjectivity on rational points; that is the separate Corollary 11.7.5 target.
