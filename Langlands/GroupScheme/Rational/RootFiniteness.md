# Conditional finiteness of actual relative roots and Weyl groups

This is an internal derived construction from the published
`HasRelativeRootSystem i` predicate in `Rational.Statement`. That predicate
remains an explicit hypothesis throughout. The module does not prove
`RelativeRootSystemStatement` or realize the relative Weyl group as a Coxeter
group.

Let `k` be a field, `T` a commutative group scheme over `k`, `G` a group
scheme with affine structural morphism, and `i : T.toGrp ⟶ G` have a
monomorphic underlying scheme morphism. No connectedness or reductivity is
assumed in this conditional construction.

`HasRelativeRootSystem.finite_relativeWeylGroup` proves that the actual
quotient `relativeWeylGroup i` is finite. A root-system automorphism is
determined by its permutation of the root indices: equal permutations give
equal weight maps on the roots, these roots span the weight space, and
Mathlib's faithful weight representation then identifies the automorphisms.
The finite index type supplied by `HasRelativeRootSystem i` therefore
makes the automorphism group, its Weyl subgroup and the image of that
subgroup finite. The predicate identifies this image with the range of the
actual `relativeWeylAction i` and asserts that this action is injective.
Finiteness consequently transfers to the original relative Weyl quotient.
This argument uses neither splitness of `T` nor the predicate's
crystallographicity and pairing-equality clauses.

`IsSplitTorus.character_toRat_injective` separately proves injectivity of
`χ ↦ 1 ⊗ χ` on the character lattice of an actual split torus. The proof
lifts the chosen group-scheme isomorphism to an isomorphism of commutative
group schemes, transports characters by `characterLattice.congr`, and
uses `splitTorus.characterLatticeEquiv` to identify them with `I → ℤ`
for finite `I`. The published `RationalSpan.toRat_injective` then applies.
This conclusion assumes splitness over the given field, not merely
geometric splitness.

With that additional hypothesis,
`HasRelativeRootSystem.finite_relativeRoots` transfers the finite rational
root image in the predicate back to the actual character-valued
`relativeRoots i`. The positive roots and `simpleRelativeRoots i ν` are
subsets of those roots, so their finiteness follows for every cocharacter
`ν`. Genericity is unnecessary for these finiteness conclusions. No
assertion that these simple roots form a root-system base is supplied.

The noncomputable constructions `relativeWeylGroupFintype`,
`relativeRootFintype`, `simpleRelativeRootFintype` and
`standardRelativeWeylGroupFintype` provide finite enumerations of the
existing quotient or subtype, with no change of underlying mathematical
objects. The last is inherited from the finite ambient Weyl group and
works for every subset parameter `J`; it adds no structural assertion
about the standard Levi. Each construction takes the root-system
hypothesis explicitly; the root enumerations also take splitness.
Consumers may install one locally with `letI`.

All proofs are elementary consequences of the named published predicates,
lattice constructions and Mathlib root-pairing and finite-set APIs.
There is no new literature assertion in this unit, and no unconditional
general reductive-group finiteness theorem is claimed.

Worker 1220 suggested the conditional finite-root, faithful-action and
split-lattice rationalization route; Worker 1107 implemented this module.
