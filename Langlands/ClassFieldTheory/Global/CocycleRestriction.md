# Restricting relative idele-class cocycle extensions

For an actual field tower `K → K' → E`, with `E` a number field, this module
restricts a normalized cocycle for `Gal(E/K)` acting on the actual idele-class
group `C_E` to the subgroup `Gal(E/K')`. The three fields have independent
universes. No Galois or number-field hypothesis on the base fields is required;
finite Galois number-field towers are included.

The two relative arithmetic actions agree after `AlgEquiv.restrictScalars`:
both are induced by the same underlying field automorphism of `E`.
`RelativeIdeleCocycle.restrictBase` evaluates the original cocycle on the two
restricted automorphisms. Its cocycle identity and normalization are inherited
from the original cocycle, with no compatibility supplied as an extra hypothesis.

`restrictionMapData` uses identity coefficients, scalar restriction on the
acting group and the constant-one cochain in the published `CocycleMap` API.
Its `restrictionInclusion` sends `(a, σ)` to `(a, σ.restrictScalars K)`.
The module proves injectivity, agreement with the coefficient inclusion,
commutation with the automorphism projection, and agreement with the standard
set-theoretic sections. The image is exactly the inverse image under the
projection of the range of `Gal(E/K') → Gal(E/K)`.

Both automorphism groups carry the explicitly installed discrete topology from
`Cocycle`. The map is continuous and an open embedding for the existing
extension product topologies: in product coordinates it is the identity on
`C_E` times the injective map of discrete automorphism groups.
`restrictionContinuousInclusion` bundles the same homomorphism and continuity.
Thus the restricted cocycle extension is realized as an actual open subgroup
of the original constructed extension with its inherited topology.

This is an internal construction from the published arithmetic action,
normalized cocycle extension and cochain-map definitions, using Mathlib's
scalar-restriction homomorphism and product topology. It makes no assertion
about the arithmetic fundamental class. In particular, identifying this
restriction with a representative chosen independently for a fundamental class
requires the separate fundamental-class restriction theorem and a cochain
comparison. Quotient transitions that change the top field, their coherence,
inverse limits and local-global maps remain separate constructions.
