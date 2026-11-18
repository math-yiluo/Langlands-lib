# A unitary action from a coherent isometric family

This internal construction takes any group and independently sized complex
inner-product spaces `E` and `H`. Its inputs are the specified linear isometries
`J(g) : E → H`, containment of each image in the image of `J(1)`, and the exact
translated Gram identity

```text
inner (J(g)x) (J(g h)y) = inner (J(1)x) (J(h)y).
```

`UnitaryEmbeddingFamily` records precisely these data. Neither space needs to
be complete, and zero spaces are allowed. It assumes no group law for
operators on `E`.

The construction first restricts `J(g)` to the actual range of `J(1)`, then
transports it through `J(1)`'s linear isometric equivalence with that range.
`embedding_transport` proves that the resulting operator has exactly the
prescribed target values. Injectivity of `J(1)` gives the identity law.

For multiplication, the Gram identity compares the two candidate target
vectors. Their norms agree because all supplied and transported maps are
isometries. Their inner product has the common squared norm, so the vectors
are equal. Injectivity of `J(1)` then gives the multiplication law. The inverse
group element proves surjectivity, producing `transportEquiv`.

`toContinuousLinearRepresentation` is the resulting homomorphism into bounded
complex-linear endomorphisms of the original `E`; it preserves the original
inner product. If the supplied maps have continuous target orbits for the
given topology on the group, the identity isometric embedding reflects
continuity of the source orbits. The common isometry bound then gives joint
continuity of the resulting action.

The provenance is internal composition of Mathlib's range equivalence for a
linear isometry, its inner-product equality criterion and the uniform
Lipschitz continuity argument. The input family is not replaced by another
one.

For cuspidal applications, actual translated embeddings, image containment,
the translated Gram identity and continuity still have to be supplied. This
generic construction alone asserts no automorphic Hilbert globalization,
smooth-vector comparison or Whittaker multiplicity one.
