# Automorphisms with prescribed simple-root scalings

Author: Worker 1467.

This internal construction is derived from `RootScalingTorus`, evaluation of
an automorphic action at a base point, and the existing comparison of action
weight spaces with actual dual-number Lie weight spaces. It introduces no
external-source assertion. The accompanying `AutomorphicActionPointIso` pair
constructs the general evaluation isomorphism and proves its differential
formula.

Let `p` be a supplied split pinning of an actual affine group scheme over any
field `k : Type u`. For every tuple `c : p.base.support → kˣ`,
`rootScalingIso c` is an actual group-scheme automorphism. It satisfies
`p.inclusion ≫ (p.rootScalingIso c).hom = p.inclusion`, and its actual linear
differential sends each supplied vector `p.pinning.rootVector a` to
`(c a : k) • p.pinning.rootVector a`.

The proof first shows that the descended action fixes the included torus on
every test scheme. An fppf local lift of a quotient point reduces this to
conjugation by an element of the supplied torus. Commutativity of the torus
makes that conjugation trivial, and the existing local-lift extensionality
lemma gives the equality before pullback.

Each chosen simple-root vector has the corresponding coordinate weight for
the descended action. Indeed, pullback of characters along the projection is
injective, and the existing restriction theorem therefore identifies the
quotient weight space with the restricted-action weight space. The restriction
is the original conjugation action, and its coordinate character pulls back
to the actual supplied simple root. The pinning's root-vector membership
then supplies the required weight equation. Smoothness needed in this
comparison comes from the supplied connected reductivity.

`rootScalingPoint c` is the base point of the simple-root split torus given
by the inverse of its affine-points equivalence. Its coordinate values are
exactly `c`. The ground-field character-value lemma checks the same fact
using global sections and the value formula for `Gm.affinePointsEquiv`;
the structural map `Spec.map (𝟙 _)` is the identity.

Finally, `rootScalingIso` evaluates the descended action at this base point.
The general evaluation formula and the all-test torus-fixation equality prove
the inclusion equation. For the differential equation, the proof converts
the action weight-space membership into the actual Lie weight-space equation,
evaluates it at `k` and the constant point, and uses that base change along
the identity algebra map fixes the Lie kernel. The character-value lemma
identifies the scalar, and `targetMapLinear_basePointIso` identifies the
evaluated differential with the differential of the actual automorphism.

The construction retains arbitrary fields and universe, the original supplied
pinning and full character lattice, central torus factors, and empty simple-root
support. It does not choose a rational lift through the original torus and
assumes no smoothness of the projection kernel. The whole pinned-isomorphism
proposition still needs its group-extension and uniqueness arguments. The
separate exact `PinnedRootScalingStatement` proof can use this construction by
taking `rootScalingIso c` and its two equations.
