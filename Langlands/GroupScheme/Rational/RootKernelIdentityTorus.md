# The split torus in the identity component of a root-kernel centralizer

This internal construction combines the published identity component of a
smooth affine group scheme with the actual torus factorization and normalizer
transport for a full character-kernel centralizer. The field `k : Type u` and
the single universe `u` are arbitrary.

Let `i : T.toGrp ⟶ G`, where `T` is a commutative group scheme over `k`.
Let `a` be any actual character of `T`, and let `j : C ⟶ G` represent the
all-test centralizer of the full scheme-theoretic kernel of `a`. Assume that
`C` is smooth and affine over `k`, and that `T.toGrp` is a split torus.
`RelativeRoot.kernelCentralizerIdentityTorus` is the actual factorization of
`T.toGrp ⟶ C` through `identityComponent C`. Its proof uses connectedness of
the split torus and `IdentityComponent.factor`. Its composite with the
identity-component inclusion is the published `kernelCentralizerTorus`; its
further composite with `j` is the original `i`.

The full kernel remains unchanged, including its nonreduced test schemes.
The character need not be nonzero, primitive, or a relative root. Neither `G`
nor `C` is assumed reductive or connected. Smoothness and affineness of `C`
are hypotheses required to form its published identity component.

If `j` is a closed subgroup, the composite `identityComponentι C ≫ j` is
closed, by composition with the published closed identity-component
inclusion. If `i` is maximal split in `G`,
`IsMaximalSplitTorus.kernelCentralizerIdentityTorus` shows that the displayed
lift, with splitness taken from this maximality hypothesis, is maximal split
in `identityComponent C`. The proof first uses maximality in `C`, then the
general maximality theorem for a factorization through a closed subgroup.

`RelativeRoot.kernelCentralizerIdentityNormalizerMap` postcomposes actual
normalizing rational points inside `identityComponent C` with
`identityComponentι C ≫ j`. It is a group homomorphism into `normalizerPoints i`.
The underlying point is precisely that composite. Representability by `j`
therefore proves that each image belongs to the original all-test
kernel centralizer. When the original torus map and its lift have monomorphic
underlying scheme maps, the corresponding Weyl-action theorem identifies
their actions on the entire actual character lattice.

The construction is derived entirely from the published
`GroupScheme.IdentityComponent`, `Rational.RootKernelTorus`, and
`Rational.MaximalSplitTorusSubgroup` interfaces. The identity-component
construction is authored by Workers 947 and 967; it is reused unchanged.
This file supplies a torus embedding and a transport map. It does not prove
smoothness or affineness of a full kernel centralizer, reductivity of its
identity component, or existence of a normalizing point with nontrivial
action. Those geometric inputs are still needed for intrinsic reflection
existence.
