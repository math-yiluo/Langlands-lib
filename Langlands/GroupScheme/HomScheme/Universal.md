# The actual relative Hom functor of group schemes

For group schemes `H` and `G` over any scheme `S`,
`HomScheme.RelativeHom H G T` consists of actual group-scheme homomorphisms
`H_T ⟶ G_T` on each test scheme `T : Over S`.
`evaluate a i` restricts a family along `a : T' ⟶ T` using the published
`Descent.pullHom`. Its source and target are the direct pullbacks along the
structural map of `T'`; the definition includes the actual
`baseChangeCompIso` and equality-of-base-map comparisons.

`relativeHomFunctor` is the resulting presheaf on all test schemes.
`IsUniversal i` says that evaluation of the actual family `i` gives a
bijection from the actual maps `T ⟶ M` to these homomorphisms, for every
test scheme. `universalIso` identifies this condition with a Yoneda
representation of the presheaf. `IsUniversal.existsUnique` exposes its
existence and uniqueness conclusion without choosing coordinates or
replacing the group schemes with abstract point groups.

## Implemented proofs and provenance

These are internal categorical constructions, not an assertion of
representability or smoothness. They use the published actual pullback
comparisons in `Descent.Data` and the all-test projection calculation
`Descent.pullHom_eval` in `Descent.DatumRelation`.
The projection, extensionality, and composition argument generalize the
published constructions in `Cartier.Restriction` from commutative group
schemes to arbitrary group schemes; no commutative Hom-group structure is
used here.

The two projections characterize `baseChangeProj`, which therefore
respects identity and composition. Projection to the original target
determines a relative homomorphism by pullback extensionality.
`evaluate_fst` computes this projection after restriction.
Identity and composition of evaluation follow from the corresponding
projection identities; these give the functor and the natural
transformation `parameterization`. The pointwise bijections in
`IsUniversal` give `universalIso`, and surjectivity and injectivity give
the unique-parameter assertion.

Finally, `isClosedImmersion_evaluate` applies the published stability of
closed subgroup inclusions under arbitrary base change, then composes
with the actual comparison isomorphisms. It places no flatness,
Noetherian, finite-type, or connectedness condition on the test maps.

## Intended use

The smooth representability assertion for a split-torus source and a
smooth affine target is a separate theorem, with SGA 3 XI, Corollary 4.2,
as its original source. This file does not prove or assume that theorem.
Its universal-family interface preserves the actual inclusion comparison
needed in pointed residue-fibre lifting.
