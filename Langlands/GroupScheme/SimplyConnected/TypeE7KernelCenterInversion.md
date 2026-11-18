# Actual E7 normalizer inversion on the full kernel centre

This internal derived result uses the actual rational normalizer and geometric
full-torus inverter constructed in `TypeE7RationalInversion`. The full centre of
the actual anisotropic kernel maps into the centre of the actual split-torus
centralizer by the published normal-reductive-centre theorem. That centralizer
centre lies in its actual maximal torus by maximal-torus self-centralization.
Both containments hold on all test schemes and pass to the separable closure.

The general same-torus-action comparison then identifies the rational
normalizer's centre action with geometric inversion. The published actual
normalizer kernel isomorphism realizes that ambient action on the particular
kernel supplied by the Tits index. Monicity of its inclusion gives inversion
on every central test point, including nonreduced tests. The theorem assumes
simply connectedness and every ordered integral E7 Cartan entry, over any field.
It does not yet assert that inversion moves a central point.

The entry proposition `Langlands.GroupScheme.TitsIndexData.E7GeometricKernelCenterInversionStatement` records the precise scope of
`exists_normalizer_inverts_geometric_kernel_center_of_E7`: its explicit hypotheses are universally quantified in a
Prop-valued definition. The implemented theorem and proof are retained.
This unit is submitted as a statement because its mathematical entry is
a proposition, rather than a data construction.
