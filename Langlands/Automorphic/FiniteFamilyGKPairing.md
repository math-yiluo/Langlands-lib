# Assembly of pairings for a finite family of commuting compact and Lie actions

This internal finite-family assembly result for Task 7294 takes a finite
family of compact-group and complex Lie algebra actions on one complex
vector space. The different local operator families commute and jointly
act irreducibly. For each family there is a supplied source model
satisfying `GKModuleDensity.Hyp`, a nonzero simultaneous intertwiner into
the target and a nonzero bilinear form invariant under the supplied
compact twist and skew-invariant under the supplied Lie twist.

The result constructs a nonzero bilinear form on the target satisfying
all local twist identities simultaneously. It does not construct any of
the local source models or their pairings.

The proof uses finite-type induction. Reindexing along an equivalence
preserves all data and hypotheses. For the empty family, any nonzero
linear functional gives a nonzero rank-one bilinear form. For a family
indexed by `Option I`, remove the factor at `none`. Genuine tensor
evaluation separates its source model from the residual simultaneous
intertwiner space. The residual operators are the commuting
postcomposition representations and Lie actions.

Residual irreducibility follows from the existing tensor image and
contraction proof. Every other source model retains a nonzero
intertwiner into the residual space by a suitable first-factor tensor
contraction. The induction hypothesis therefore supplies a nonzero
pairing invariant under all remaining local twists. Tensor that form
with the removed factor's supplied pairing and transport it through the
evaluation equivalence. The tensor covariance identities verify the
compact and Lie identities both at the removed place and at every
remaining place.

The source-model universe is included in the target-carrier universe,
so taking simultaneous multiplicities does not increase the carrier
universe during induction. All index, group, Lie and source universes
are free. No topology or local-finiteness assumption is imposed on the
target beyond the stated actual actions; the density hypotheses belong
to the supplied local source models.

`assemblePairing` chooses the constructed bilinear form together with its
nonzeroness and every local compact and Lie identity. Its inputs retain
precisely the supplied source models, their pairings, target action
commutation, joint irreducibility and nonzero local intertwiners.
