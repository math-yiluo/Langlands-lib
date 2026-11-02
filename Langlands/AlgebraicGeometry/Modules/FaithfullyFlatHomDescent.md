# Descent of compatible ordinary module morphisms

For arbitrary schemes `X` and `Y` in universe `u` and a morphism
`p : X ⟶ Y`, `PullbackHomCompatible p a` is the actual overlap condition on a
morphism `a : p* M ⟶ p* N` of ordinary module sheaves. For every scheme `U`,
every pair `s,t : U ⟶ X`, and every equality `s ≫ p = t ≫ p`, it requires
`s* a ≫ E(N) = E(M) ≫ t* a`. Here `E` is the published
`equalCompositeIso`, formed from the ordinary pullback composition
isomorphisms and transport along that equality. Every scheme test is included.

Naturality of `equalCompositeIso` proves `compatible_pullback`: the pullback
of every morphism on `Y` has this compatibility, without geometric assumptions.

The remaining lemmas lie in the namespace `FaithfullyFlatHomDescent`.
For an affine `p` and a quasi-coherent target `N`,
`coalgebra_hom_condition` turns compatibility on the actual kernel pair
`X ×_Y X` into the morphism equation for the coalgebras of the specified
ordinary pullback-pushforward adjunction. The source `M` is arbitrary.

The implemented comparison uses `s = pullback.fst p p` and
`t = pullback.snd p p`. Write `B(Q)` for the actual base-change map
`p* p_* Q ⟶ t_* s* Q` and `E(Q)` for the canonical comparison
`s* p* Q ≅ t* p* Q`. The existing adjunction identity
`pullback_map_unit_comp_pushforwardBaseChange` says that
`p* η_p(Q) ≫ B(p*Q) ≫ t_* E(Q)` is `η_t(p*Q)`.
For `Q = N`, the two maps after `p* η_p(N)` are invertible: affine base
change applies because `p* N` is quasi-coherent, and `E(N)` is an
isomorphism. Cancelling their composite reduces the desired coalgebra
equation to the naturality of `B`, the given geometric overlap equation,
the displayed unit identity for `M` and `N`, and naturality of `η_t`.
Thus the proof uses the specified base-change map throughout.

When `p` is also flat and surjective, `existsUnique_hom_of_kernelPair`
constructs the coalgebra morphism with underlying map `a`. The published
equivalence `isEquivalence_modulePullbackComparison p` supplies its preimage
`b : M ⟶ N`. The comparison functor maps `b` to `a`, and faithfulness of
ordinary pullback gives uniqueness. The lemma `existsUnique_hom` applies this
result to `PullbackHomCompatible`.

Under the same assumptions, `existsUnique_iso` says that every compatible
isomorphism `e : p* M ≅ p* N` is the pullback of a unique isomorphism
`b : M ≅ N`, with the equality `(pullback p).mapIso b = e`. It first
descends `e.hom`. Conservativity of ordinary pullback along a flat surjection
makes the descended morphism invertible, and uniqueness of its underlying
morphism gives uniqueness of the isomorphism. Quasi-coherence is required
only for `N`, including in this isomorphism result.

This is an internal derived unit. Its inputs are the Library's actual
equal-composite comparisons, the adjunction unit identity in
`DerivedRestriction`, affine pushforward base change in
`AffinePushforwardBaseChange`, and the ordinary module comparison equivalence,
faithfulness and conservativity in `FaithfullyFlatPullbackDescent`.
There is no new original-literature assertion used as a premise.

The results preserve arbitrary universe `u`, arbitrary schemes and ordinary
module sheaves. They establish descent of morphisms between modules already
on the base. Effectivity of general geometric object cocycles, preservation
and detection of the coherent-family conditions, and the smooth scheme atlas
remain separate obligations of the host task.
