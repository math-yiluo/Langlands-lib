# Scalar extension across atlas saturation

`CompleteUltrametricField.localizedSaturationExtendIso` compares two
functors from the localized compatible category over \(K\) to the
localized saturated category over \(L\). One saturates over \(K\) and
then extends scalars. The other extends scalars using `localizedExtend`
and then saturates over \(L\). The complete ultrametric fields have a
common carrier universe. At both ends the ambient and chart-index
universes are `max u v`, where `u` is the field universe. The field
arrow is an isometric embedding and supplies the normed algebra
instance for the saturated scalar-extension functor.

Let \(S\) denote saturation and \(I\) the forgetful functor on saturated
atlases. The natural isomorphism \(S\circ I \simeq \mathrm{id}\), written in
Lean as `compatibleFunctor ⋙ saturationFunctor ≅ 𝟭 _`, comes from
`SaturatedAtlasPresentation.saturationComparisonNatIso`. At each
compatible atlas \(A\), its component at \(S(A)\) lifts through the
fully faithful \(S\) to an isomorphism \(I(S(A))\simeq A\). Faithfulness
also gives naturality, by testing the square on \(S(f)\).
Postcomposition by extension of compatible atlases, target saturation,
and the target localization gives the comparison before source
localization. The strict localization factorization equations
identify the two functors to be compared on the source localization.
`Localization.liftNatIso` then gives the isomorphism on all localized
objects and morphisms.

The comparison concerns the atlas presentations of the ground-field
functor in Berkovich, *Étale cohomology for non-Archimedean analytic
spaces* (1993), §1.4, printed p. 30 (PDF p. 27). The registered source
`berkovich-1993-etale-cohomology` has SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The use of the saturation equivalence and the descent of its comparison
are internal to the atlas localizations.
