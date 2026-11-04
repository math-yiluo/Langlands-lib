# Actions preserving a finite additive generating set

This internal supporting construction restricts an action by additive
automorphisms to an invariant set. It is derived directly from Mathlib's
additive subgroup closure, permutation and finite-type interfaces. Its
intended application is the full character-lattice action of a normalizer
on the finite generating weight set of a faithful representation.

For an arbitrary additive group `M`, a group `H` and a homomorphism
`ρ : H →* Multiplicative (M ≃+ M)`,
`generatorPermutation ρ S hstable` is the homomorphism
to permutations of `S` induced by restriction. The hypothesis `hstable`
requires every group element to map `S` into itself. The inverse group
element supplies the inverse restricted permutation. Neither finiteness
nor generation is required for this construction. The `Multiplicative` tag
uses composition as multiplication on Mathlib's additively written `AddAut M`.

If `AddSubgroup.closure S = ⊤`, `generatorPermutation_eq_iff` says that two
restricted permutations agree exactly when the original automorphisms
agree. The proof obtains equality on `S` by evaluation and extends it to
the additive subgroup closure using `AddMonoidHom.eq_of_eqOn_dense`.
Consequently a faithful original action restricts faithfully.

`finite_of_preserves_generating_set` then embeds `H` into the permutation
group of the finite set `S`. The image version
`finite_range_of_preserves_generating_set` applies this result to the
inclusion of `ρ.range`; faithfulness of the original action is unnecessary.
No freeness, torsion-freeness or commutativity assumption is needed on `M`.

For modules, `linearAutToAddAut` forgets scalar compatibility, and its
injectivity follows by pointwise extensionality. The companion
`finite_linear_subgroup_of_preserves_generating_set` applies the additive
result to a subgroup of linear automorphisms of an arbitrary module over a
semiring. Its generating hypothesis is still additive generation, rather
than module generation. `finite_linear_range_of_preserves_generating_set`
provides the corresponding image result for any homomorphism into linear
automorphisms, without a faithful-action assumption.

The construction does not prove that any geometric normalizer preserves
a particular weight set or that those weights generate the character
lattice. These are separate hypotheses for the intended application.
