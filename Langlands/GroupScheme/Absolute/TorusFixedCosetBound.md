# Bounding torus-fixed quotient points by the actual Weyl quotient

For a field `k : Type u`, let `i : T.toGrp ⟶ G` be a maximal torus,
`j : P ⟶ G` a closed subgroup, and `q : G.X ⟶ Q` a morphism whose fibers
have the exact right-coset relation on every test scheme:
`g ≫ q = h ≫ q` if and only if `g⁻¹ * h` belongs to the range of `j`.
Assume a homomorphism `f : T.toGrp ⟶ P` with `f ≫ j = i` and conjugacy
of maximal tori inside `P`, in the precise sense of
`MaximalToriAreConjugate P`.

`exists_normalizer_representative_of_torus_fixed_coset` proves that every
rational `g` whose coset is fixed on all tests has a representative in
`normalizerPoints i`. The published `factorOfFixedCoset` factors
`i ≫ Int(g⁻¹)` through `P`. Maximality transports through the closed inclusion
and the inner automorphism, so both this factor and `f` are maximal tori in
`P`. The conjugacy hypothesis supplies `p ∈ P(k)` and a torus automorphism.
Naturality of inner conjugation then proves that `g p` normalizes `T`.
The exact fiber relation proves that it has the original quotient point.

Assume also that `centralizerPoints i` lies in the range of `P(k)`.
`relativeWeylCosetMap` sends the actual rational Weyl quotient
`relativeWeylGroup i = N(k)/Z(k)` to `Q(k)` by sending a normalizer
representative `n` to `n ≫ q`. Its well-definedness uses the centralizer
containment and the exact fiber relation. `relativeWeylCosetMap_mk` records
its value on representatives.

Let `a : SchemeAction T.toGrp Q` be an action with
`a.act t (g ≫ q) = ((t ≫ i.hom.hom) * g) ≫ q` on every test scheme.
Assume that `G(k) → Q(k)` is surjective. Fixedness here is exactly
`a.IsFixed x`: the point remains fixed by the whole torus after every
change of test scheme, including nonreduced tests.
`exists_relativeWeylCosetMap_eq_of_isFixed` pulls this fixedness back along
the structural morphism of each test scheme and applies the normalizer
representative theorem to a rational lift of `x`.

`torusFixedPointWeylEmbedding` chooses a Weyl preimage for each such fixed
rational point. This is an injection because applying `relativeWeylCosetMap`
recovers the original point. If the actual Weyl quotient is finite,
`finite_torusFixedPoints` and `card_torusFixedPoints_le_relativeWeylGroup`
deduce finiteness and the corresponding `Nat.card` upper bound.

These are internal deductions from the published fixed-coset factorization,
maximal-torus transport, inner-conjugation identities and elementary quotient
and cardinality facts in Mathlib. There is no restriction on the field,
characteristic, splitness or universe beyond the displayed hypotheses.
The module does not prove conjugacy inside `P`, centralizer containment,
rational lifting, existence of an equivariant quotient, or Weyl finiteness;
each is an explicit input where needed. In particular, it is a focused
helper for the rank-one task, not the unconditional positive-root uniqueness
theorem or a dimension lower bound.
