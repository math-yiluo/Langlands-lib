# Finite torus restrictions and actual cocharacters

Author: Worker 1375.

This internal supporting unit proves the cocharacter injectivity needed for
`CentralIsogenyRootDatumHomStatement`. It uses the published cancellation
theorem for finite homomorphisms and ordinary properties of finite scheme
morphisms. It introduces no proposition assumed as an axiom.

All results hold over an arbitrary field `k : Type u`. The commutative group
schemes `T` and `T'` need not be tori.

`cocharacterMapInt_injective_of_isFinite` says that a finite homomorphism
`t : T → T'` induces an injective map on the actual integral cocharacters
`Hom(𝔾_m, T) → Hom(𝔾_m, T')`, by postcomposition with `t`. The multiplicative
group is split, hence smooth, affine and connected. If two cocharacters have
the same composite with `t`, `finiteHom_cancel` from
[`CentralIsogeny.Uniqueness`](Uniqueness.md) identifies the underlying group
homomorphisms. Changing to the additive notation of commutative group
homomorphisms gives equality of the original cocharacters. The cancellation
theorem works over arbitrary fields by passing to an algebraic closure and
descending equality. No smoothness or reducedness of `t` or its kernel is
required.

`cocharacterRangeEquivOfFinite` identifies the source cocharacter lattice
with the range of the same actual postcomposition map. It is an integral
linear equivalence, constructed by `LinearEquiv.ofInjective` from the
preceding theorem. Its forward map, after forgetting range membership, is
exactly `ν ↦ ν ≫ t`, as `cocharacterRangeEquivOfFinite_apply` states. Its
inverse sends an element of the image to its unique source cocharacter.
This construction makes no claim that the range is the whole target
lattice.

`isFinite_torusRestriction` considers closed subgroup embeddings
`i : T → G` and `i' : T' → G'`, a finite homomorphism `φ : G → G'`, and
`t : T → T'` with `i ≫ φ = groupHom t ≫ i'`. The composite `i ≫ φ` is finite,
because a closed immersion is finite and finite morphisms compose. The
closed immersion `i'` is separated, so Mathlib's `IsFinite.of_comp` makes
`t` finite. This lemma requires neither centrality nor maximality.

`IsCentralIsogeny.cocharacterMapInt_injective_of_square` combines those two
results using finiteness of the supplied central isogeny. Its map is the
published `RealTorusSpace.cocharacterMapInt t`, whose value at `ν` is `ν ≫ t`.
It requires only the two closed subgroup embeddings and the commuting
square; splitness, reductivity and maximality are unnecessary for this
particular conclusion.

These are derived internal lemmas. They establish neither the root
bijection nor coroot compatibility, character injectivity, or the
isomorphism criterion, and do not prove the whole host proposition.
