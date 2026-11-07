# Normalization of the actual Levi Jacquet completion

Author: Worker 1775. Module
`Langlands.Representation.Exponents.LeviJacquetCompletionNormalization`, namespace
`Langlands.Aubert.General.RepresentedParabolic`.

This derived supporting construction compares the completion of the published
`leviJacquetFunctor` with that of the unnormalized radical coinvariants on the
actual rational points of its Levi. Its source context is David Renard,
*Représentations des groupes réductifs p-adiques*, edition dated 9 July 2026,
I.1.4, printed p.9 / PDF p.15, VI.1.2, printed pp.135–136 / PDF pp.141–142,
and VI.9.7, printed pp.205–206 / PDF pp.211–212. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The VI.9.7 statement's normalization note explicitly identifies this comparison
as an outstanding supporting step.

The field universe `u` and representation carrier universe `v` are independent.
The inputs are a Hausdorff topological field, an affine ambient group scheme
whose rational points with their canonical topology are locally compact and
nonarchimedean, and an actual represented parabolic triple with rational Levi
and geometric unipotent radical. The comparison with the published normalized
functor retains its multiplication-isomorphism parameter. No local-field,
connected-reductive ambient, opposite-parabolic, admissibility, finite-length,
cofinality, contraction or stabilization premise is used. Levi points carry the
published `leviPointTopology`; their topological group structure follows from
`leviPoints_nonarchimedeanGroup`.

`leviUnnormalizedJacquetFunctor` takes the actual radical coinvariants, with
character `1`, by `Jacquet.Localization.smoothFunctor`, then pulls back the Levi
image action along the continuous `leviPointsEquiv`. Its carrier is literally
the same quotient as the normalized functor. The representation equality
`leviJacquetFunctor_obj_representation_twist` identifies the latter action with
the former twisted by the pullback of `HaarModulus.closedInverseHalfCharacter`
for the actual closed radical image and normalizing Levi image.

`leviJacquetFunctor_averageMap_eq` proves equality of normalized compact-open
averages for every compact open subgroup of the actual Levi points. The
continuous Levi equivalence pulls back the positive Haar character with open
kernel; its value is one on compact subgroups by the published positive-character
triviality theorem. The generic closed Haar comparison therefore applies
without any additional character-triviality hypothesis.

`leviJacquetCompletionNormalizationEquiv` specializes
`CompactCompletion.closedInverseHalfTwistEquiv` to these exact functors. Equality
of their averages identifies their compatible-family completion subspaces.
Both directions keep every component unchanged, as the two application lemmas
state. This is a linear equivalence of the completion spaces; no smoothness of
the completed group action is asserted.

This implements the normalization comparison needed for Renard VI.9.7, using the
existing compact-open completion model of I.1.4. It does not identify the
radical-fixed ambient completion with either Jacquet completion, prove
parabolic cofinality or stabilization, or prove either exact target of the
parent task. Those obligations remain open.
