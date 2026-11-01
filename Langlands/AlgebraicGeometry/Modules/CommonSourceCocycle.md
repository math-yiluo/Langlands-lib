# Coherent overlap identifications induced by a common module

This is a derived construction from the Library's actual scheme-module pullback
functors. It uses their published associativity (`compHom_assoc`), their canonical
square comparisons (`squarePullbackIso`), and the square comparison's compatibility
with a further pullback (`squarePullbackIso_comp`). No new mathematical premise
or literature-dependent definition is introduced.

For commuting maps `f : V ⟶ Ua`, `g : V ⟶ Ub`, `a : Ua ⟶ X`, and `b : Ub ⟶ X`,
with `f ≫ a = g ≫ b`, fix a module `N` on `X` and actual module isomorphisms
`ea : a* N ≅ Ma` and `eb : b* N ≅ Mb`. The definition
`CommonSourceCocycle.transition` is the actual overlap isomorphism
`f* Ma ≅ g* Mb`: it first pulls back the inverse of `ea`, applies the canonical
square comparison for `N`, and then pulls back `eb`.

`transition_cocycle` proves the full triple-overlap cocycle for these maps on
any commuting diagram of three pairwise overlaps and one common comparison
scheme. It explicitly includes all canonical square comparisons between the
iterated pullbacks. No open immersion hypotheses are needed for this identity,
and no distinctness of the three charts is assumed. Specializing to the actual
pairwise and triple pullbacks of an arbitrary scheme open cover gives
`openCover_cocycle`, whose conclusion is exactly the Library's
`OpenCoverModuleGluing.CocycleCondition`.

The proof uses normalization into the pullback of `N` along one fixed map from
the triple-overlap scheme to `X`. The map `normalize` compares a threefold
pullback with that fixed pullback. `normalize_eq` permits composition of the
first two maps instead of the last two. The lemmas `inner_square_normalize` and
`outer_square_normalize` show that replacing either pair by the other side of
a commuting square preserves normalization. Canceling a common invertible
normalization proves `canonical_cocycle` for the canonical pullbacks of `N`.
For the arbitrary pieces, `pieceNormalize` first uses the inverse of the chosen
piece isomorphism. Naturality of the square comparison and cancellation of a
piece isomorphism with its inverse give the corresponding two normalization
identities. These prove `transition_cocycle` by the same cancellation argument.

All schemes and modules are in arbitrary universe `u`. This helper verifies
coherence when the pieces are already identified with pullbacks of a common
module. It does not construct an extension across an open immersion or assert
that arbitrary pairwise isomorphisms satisfy a cocycle.
