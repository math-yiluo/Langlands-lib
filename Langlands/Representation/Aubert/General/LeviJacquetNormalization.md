# Ambient normalization of the actual Levi-in-Levi Jacquet functor

This internal construction transports the published Levi-in-Levi Jacquet
normalization through the actual subgroup identification. Its provenance is
the definitions in `Aubert.General.Parabolic` and the proved Haar transport
laws in `Aubert.General.SubgroupOfModulus`.

For subgroups `N ≤ M` and `L ≤ M`, `normalizes_of_subgroupOf` derives
`L ≤ normalizer N` from normalization of `N.subgroupOf M` by
`L.subgroupOf M`. It places each element of `L` inside `M` and applies the
published `subgroupOfNormalizerMap`. This part needs only a group.

Let `G` be a locally compact nonarchimedean group, with closed `N`.
The functor `leviAmbientNormalizedJacquetFunctor` first takes the actual
trivial-character localization by `N.subgroupOf M`, with output action by
`L.subgroupOf M`. It then pulls the output action back along
`(subgroupOfContinuousEquiv hLM).symm` and twists by the actual ambient
`HaarModulus.closedInverseHalfCharacter N hN L`. The normalizer premise for
this character is derived by the preceding lemma. Its open kernel is the
published open-kernel result for this actual Haar character.

`leviInverseHalfCharacter_eq` identifies the inside inverse half-character
evaluated at the copy of `l : L` with this ambient character at `l`. Its proof
specializes `closedInverseHalfCharacter_subgroupOf` and cancels the continuous
equivalence with its inverse. The local compactness of `M` in this comparison
comes from its closedness.

For closed `M`, given the same inside semidirect decomposition `Q = L ⋉ N` used by the
published `leviNormalizedJacquetFunctor`,
`leviNormalizedJacquetAmbientIso` gives a natural isomorphism to the new
functor. Every component is the identity linear equivalence on the original
localization quotient, with the actions identified by the preceding character
equality. The proof first uses `MonoidHom.ext` and
`leviInverseHalfCharacter_eq` to identify the entire pulled-back character.
It then composes the functor associator with a left whiskering of
`Langlands.Derivative.DeterminantTwist.pullbackTwistIso` and
`Langlands.Derivative.DeterminantTwist.twistCongrIso`. The first generic
isomorphism moves the inside twist through pullback; the second replaces its
pulled-back character with the actual ambient inverse half-character.
The `continuousPullbackFunctor` used by that generic API is definitionally
the same pullback as `SmoothRep.pullbackFunctor` here. Those generic
isomorphisms supply naturality. The carrier universe `uV` is independent of
the group universe `uG` and is unchanged.

This construction proves only transport of the same radical's normalization
between two ambient groups. It does not identify distinct radicals, establish
either orbit Haar correction, cancel their product, identify graded pieces,
or prove compact/full induction comparison or the rational geometric K0
expansion. Its proof bodies use no geometric lemma, adjointness, cuspidal
support, character independence, or classification theorem. The actual
Haar-character comparison depends on
`Geometric.haarChar_eq_of_conjugacy` through `SubgroupOfModulus`; it compares
the same radical in two ambient groups. The two reused twist isomorphisms
are generic in their groups and characters and use no determinant or
general-linear derivative theorem. The import closure contains the existing
normalized representation constructions and
`GeneralLinearDerivativeDeterminantTwistProof`, including its
general-linear-specific results; only its two generic twist isomorphisms
are used in this proof.

Author: Worker 1263.
