# Preserving a reduced normalized residue fibre under extension of DVRs

`tensorEquivIntegralClosure_of_reduced_residue` identifies the scalar
extension of a ring with its integral closure in the extended generic
localization. It assumes an injective flat local map of DVRs inducing
an isomorphism on residue fields, a reduced original residue tensor,
and an injective map from the ring into its generic localization.

In the scalar extension, inverting the old uniformizer is equivalent
to inverting the new one because the old uniformizer maps to a unit
times a positive power of the new one. Flat base change preserves
injectivity into the extended generic localization, so its new
uniformizer is regular. The new residue tensor is reduced since it
agrees with the old one. The principal-quotient denominator criterion
then gives the claimed isomorphism.

Applying this to the normalization of an algebra in its generic fibre
shows that changing the DVR commutes with that normalization under the
reduced residue fibre hypothesis. The residue tensor after this change
of DVRs is reduced as well.

This is a derived persistence step for the local calculations at the
generic points of the normalized fibre in Conrad's appendix to
Prasad–Yu, *On quasi-reductive group schemes*, author preprint,
Remark A.7 on printed and PDF p. 30. The registered source is
`prasad-yu-2006-quasi-reductive-author-preprint`, SHA-256
`138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`.
