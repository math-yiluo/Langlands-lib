# The actual Steinberg product as a translated independent-weight product

This internal reduction works over every field `k : Type u`, for the actual affine
group scheme `G` and supplied split pinning `p`. It uses the supplied simple-root
maps `x`, supplied simple-reflection representatives `n`, and any ordering `e` of
the simple roots. It does not choose new representatives or root maps.

On every scheme test `T`, write `N_j` for the product of the representatives
strictly preceding index `j`, and `N` for their full ordered product. The group
identity for interleaved products gives

```text
product_j (x_j(c_j) n_j) = (product_j N_j x_j(c_j) N_j^-1) N.
```

The proof transports both the prefix products and the full product from the
normalizer subgroup to the group of `T`-points using the subgroup inclusion and
the constant-point homomorphism. The conjugate factors are exactly the existing
`prefixRootHom` maps. Evaluating at the universal affine-space coordinates then
identifies the actual `steinbergProduct` morphism with
`IndependentWeightProduct.morphism (prefixRootHom e x n)` followed by right
translation by `coxeterNormalizer e n`.

The final theorem assumes `IndependentWeightProductImmersionStatement` and derives
the exact `SplitSteinbergImmersionStatement`. It applies the criterion to the
pinning's actual split torus, its conjugation action on `G`, the prefix-root maps
and their integral character weights. The published prefix-factor construction
supplies closedness of each map, equivariance on every scheme test, and linear
independence over the integers. Right translation is a scheme isomorphism, so
composition preserves the resulting closed immersion. The empty ordering is
included by the finite-product identity and the general criterion. The target's
semisimplicity premise is retained, although the reduction does not need it.

This is a derived internal construction and conditional theorem. Its provenance
is the elementary group identity in `Langlands.Algebra.OrderedPrefix`, the actual
prefix constructions in `SteinbergPrefixWeights`, and the previously defined
right-translation isomorphism. It does not itself prove the independent-weight
criterion or an unconditional split immersion theorem.
