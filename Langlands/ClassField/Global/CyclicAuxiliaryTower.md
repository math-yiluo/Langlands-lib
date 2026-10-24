# Cyclic auxiliary towers for global invariant descent

For number fields `F` and `E` in an arbitrary common universe `u`, with `E/F`
Galois, and every positive natural number `n`, this module constructs fields
`K` and `L` in the same universe with compatible towers
`F → E → L` and `F → K → L`. The extension `K/F` is cyclic Galois of degree
exactly `n`, `L/F` is Galois, and `L/E` is cyclic Galois.

## Construction and interface

`CyclicAuxiliaryTower F E n` bundles the auxiliary field `K`, the overfield `L`,
their field and number-field instances, their algebra structures, the two
scalar-tower witnesses, cyclicity of `K/F` and `L/E`, Galoisness of `K/F` and
`L/F`, and the equality `[K:F] = n`. Its projections are instances where
appropriate. Galoisness of `L/E` follows from the Galois tower theorem and is
also supplied as an instance.

`cyclicAuxiliaryTower F E hn`, for `hn : 0 < n`, constructs such a bundle.
It chooses `K` using the published `Langlands.Global.exists_cyclic_extension`,
then takes the published `commonGaloisOverfield F F E K` for `L`. The returned
bundle exposes one base algebra structure and the compatible `E` and `K`
algebra structures. This keeps both towers available directly to cohomology
maps without choosing new embeddings.

The structure specifies the properties above; it does not require an arbitrary
inhabitant to be a minimal compositum. The construction uses a compositum.
It imposes no linear-disjointness condition, and it does not assert that
`[L:E] = n`.

## Compositum lemmas and proofs

`commonGaloisOverfield_generated F B L₁ L₂` concerns the existing construction
for two Galois number-field extensions `L₁/F` and `L₂/F` with compatible
embeddings of a common number field `B`. It proves that the two field ranges
inside the chosen common overfield have supremum equal to the top intermediate
field. The proof unfolds the construction, which embeds both fields into an
algebraic closure of `B` and takes the supremum of their ranges. Mapping the two
ranges back into that closure gives exactly the two original ranges. Injectivity
of intermediate-field mapping proves the desired equality.

`commonGaloisOverfield_isCyclic_left F B L₁ L₂` adds cyclicity of `L₂/F` and
proves cyclicity of the chosen overfield over `L₁`. Its private general helper
uses the actual restriction homomorphism from `Gal(L/L₁)` to `Gal(L₂/F)`.
An automorphism in its kernel fixes the image of `L₂`; it already fixes `L₁`.
The intermediate field on which it agrees with the identity therefore contains
both images, and the generation equality makes this field all of `L`.
Restriction is injective, so cyclicity follows from that of `Gal(L₂/F)`.
This argument needs no disjointness assumption.

## Provenance and scope

This is a derived supporting construction. It combines the published
`CommonGaloisOverfield` and `CyclotomicAuxiliary` constructions with Mathlib's
intermediate-field maps, restriction of normal-field automorphisms, and the
fact that a group embedded in a cyclic group is cyclic. The new argument is
the generation equality and the injectivity of restriction; the exact-degree
existence theorem is reused unchanged.

Taking `n = Module.finrank F E` supplies the arithmetic tower needed in the
general global invariant descent. This module does not construct cohomology
classes or their invariants, prove a cohomological descent theorem, or prove
`GlobalInvariantStatement`.
