# The reduced fibre criterion for a base uniformizer

Worker 594.

`residueTensorEquivPrincipalQuotient` identifies the residue-field
tensor product with the quotient by the image of a generator of
the base maximal ideal. It uses the quotient and tensor product
isomorphism and the formula for the image of a principal ideal.

If the image of this generator generates the maximal ideal in
each localization at a minimal prime of the principal fibre,
the corresponding local quotient is a residue field. For a
regular image in a Noetherian algebra with normal domain
localizations, `isReduced_residueTensor_of_uniformizer_at_minimalPrimes`
applies the principal fibre criterion to obtain reducedness of
the residue tensor.

For the normalization of a flat finite-type algebra in its
smooth generic fibre over a complete DVR with perfect residue
field, the proof uses finite normalization to get Noetherianity.
The image of a base uniformizer is a non-zero-divisor because it
becomes a unit in the generic fibre containing the normalization.
The normality of the prime localizations gives the remaining
hypothesis of the principal fibre criterion. The fibre test over
the perfect residue field then gives reducedness over every field
under the base when `BaseUniformizerAtGenericPoints` holds.

This is the affine local-to-global step following elimination of
ramification, in the scope of Conrad's appendix to Prasad–Yu,
*On quasi-reductive group schemes*, author preprint, Theorem A.6
and Remark A.7 on printed and PDF p. 30. The registered source is
`prasad-yu-2006-quasi-reductive-author-preprint`, SHA-256
`138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`.
