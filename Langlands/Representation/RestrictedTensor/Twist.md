# Scalar characters and genuine restricted tensor twists

This internal construction uses the existing algebraic direct limit
`RestrictedTensor.Space K V E e` and the actual cofinite restricted product
`RestrictedGroup G H`. The index, local groups, field, and vector carriers
have independent universes. The coefficient field `K` is arbitrary. No
topology, finite dimension, nonzeroness, smoothness, or irreducibility of
the vector carriers is required.

The character lemmas first allow a general commutative monoid target.
`localCharacter H χ i` restricts the given group character along the
existing identity-supported singleton insertion. The finite projection
formula `character_finiteProjection` follows by induction on the finite
set using the published singleton-insertion formula.

For a finite set `E`, the full reference tail is the existing subgroup of
tuples equal to one on `E` and integral outside `E`. Enlarging `E` shrinks
this subgroup, as `tailReferenceSubgroup_le_of_subset` proves. If `χ` is
trivial on this full subgroup, `character_eq_prod_of_tail` proves

```text
χ(g) = ∏ i ∈ S, χ(singleton i (g i))
```

for every finite `S` containing `E` and every `g` integral outside `S`.
The proof factors `g` into its actual finite projection and complementary
tail; the tail value is one. `localCharacter_eq_one_of_tail` applies the
same hypothesis to a single integral coordinate outside `E`.
Triviality on individual local integral subgroups alone is not substituted
for full-tail triviality.

With topologies on the local groups and open reference subgroups,
`exists_character_tail` proves that a locally constant character is
trivial on some full reference tail. It applies the published identity
neighborhood extraction to the open fiber of one. This result does not
assume compactness or assert that an arbitrary continuous character is
locally constant.

For the tensor constructions the character takes values in `Kˣ`. The
original reference vectors `e i` are fixed by `ρ i` on `H i` outside `E`,
and full-tail triviality is explicit. `twistReference_fixed` proves that
these same vectors are fixed by the existing scalar twists
`Langlands.twist (localCharacter H χ i) (ρ i)`. Thus
`twistedRepresentation` is the genuine restricted tensor action of these
local twists on the same direct-limit carrier, with its invariance law
proved.

`twistedRepresentation_eq` proves equality of this action with the
existing global scalar twist of `representation H ρ E e he`. For each
group element the proof passes to cofinal finite stages containing its
nonintegral coordinates. The component action formula and multilinearity
extract the product of local scalars, and the proved character
factorization identifies that product with `χ(g)`. The proof includes
empty finite stages and does not require nonzero reference vectors.
`twistEquiv` bundles the comparison as an actual equivariant linear
equivalence; its underlying linear map is the identity.

Provenance is internal: finite projection and tail factorization,
the existing neighborhood theorem, multilinearity of finite tensor
products, cofinal direct-limit extensionality, and the published scalar
twist suffice. There is no new original-literature identification.
No automorphic occurrence, arbitrary tensor factorization, automatic
finite ramification, Satake normalization, or global association result
is asserted here.
