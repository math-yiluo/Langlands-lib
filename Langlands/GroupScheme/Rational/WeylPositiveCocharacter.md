# Positive central cocharacters by integral Weyl averaging

This is derived infrastructure for the minimal-parabolic Levi-centralizer
proof. It uses the published actual normalizing automorphisms, lattice pairing,
relative reflections, normalized tangent support and root-annihilator centrality.
It does not prove the geometric existence of a relative root-system realization.

Work over any field `k` in an arbitrary universe `u`. Let `t : T → M` be an
actual homomorphism from a commutative group scheme whose underlying scheme
map is monic. No splitness or reductivity is needed for the lattice action.

`normalizerCocharacterAction` postcomposes cocharacters with the actual torus
automorphism of a rational normalizing point. Uniqueness of that automorphism
gives the multiplication law. Centralizing points act trivially, so
`relativeWeylCocharacterAction` descends to the actual quotient
`relativeWeylGroup t = N_M(T)(k)/Z_M(T)(k)`. The actual character and cocharacter
actions preserve the integral pairing. The right-action pairing formula moves
an action on a cocharacter to the inverse action on a character.

Given a finite enumeration of this actual quotient,
`relativeWeylCocharacterSum t` is the integral linear operator

```text
ν ↦ ∑ w : relativeWeylGroup t, relativeWeylCocharacterAction t w ν.
```

There is no division by the group order. Reindexing the finite sum by left
multiplication proves that it is fixed by every Weyl class. If a character
family `Φ` is preserved by every class and every member pairs strictly positively
with `ν`, every summand in the pairing formula is strictly positive. The finite
group is nonempty, so the pairing with the integral sum is strictly positive.
This argument requires no negation closure, nonempty character family or
nonzero-character premise.

Now assume `M` is affine and `T` is split. A supplied actual relative reflection
in a root negates its rationalized root vector. Injectivity of rationalization
on the actual character lattice upgrades this to negation of the integral
root character itself. If every actual relative root has such a reflection,
pairing invariance and fixedness of the orbit sum identify its pairing with
a root with its own negative. It is an integer, so it is zero.

If additionally `M` is smooth and connected, the published
`rootAnnihilatorCentrality` theorem turns these zero pairings into centrality
of the actual composite `Gm → T → M` on every test scheme. Neither reductivity
nor maximality of `T` is needed for this implication.

The final theorem `HasRelativeRootSystem.exists_centralCocharacter_positive`
applies this construction to the actual tangent-weight support of a subgroup
functor `F` of an affine group scheme `G`, with `j : M → G`. It assumes the
whole-test normalization predicate for conjugation along `j`. The published
normalizer-support theorem supplies invariance of that support under the
actual quotient. The supplied `HasRelativeRootSystem t` gives both finiteness
of the quotient and existence of its root reflections. Thus any actual
cocharacter strictly positive on the original support yields an actual
cocharacter central in `M` and strictly positive on the same support.

The final result retains splitness of `T`, smooth connected affine `M`, the
given root-system realization, whole-test normalization, and a supplied initial
positive direction. It does not construct the root-system realization or the
initial positive direction, descend the cocharacter over a nonsplit field,
establish ambient maximal splitness, or prove the Levi-centralizer target.
