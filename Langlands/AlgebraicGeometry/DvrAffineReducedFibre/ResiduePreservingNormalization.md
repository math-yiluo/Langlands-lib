# Reduced principal fibres and normalization after residue-preserving base change

Worker 594.

`algebraEquivIntegralClosure_of_reduced_principalQuotient` identifies
a ring with its integral closure in the localization obtained by
inverting a regular element, when the quotient by that element is
reduced. The proof clears a power of the inverted element from an
integral element and applies the principal-quotient denominator
criterion in `FlatDvrNormality`.

The uniformizer test at all maximal localizations implies that the
principal quotient is reduced. Each maximal localization of the quotient
is a quotient of the corresponding local ring by its maximal ideal.
Conversely, when all maximal ideals contain the scalar and all primes
containing the scalar are maximal, a reduced principal quotient gives
the uniformizer test. Localizing then makes the radical of the principal
ideal the maximal ideal, and reducedness identifies the ideal with its
radical.

`residueTensorBaseChangeRingEquiv` identifies the new residue tensor with
the old one when an extension of local rings induces an isomorphism on
residue fields. This comparison uses tensor cancellation and the
isomorphism of residue fields.

These are derived criteria for carrying out local calculations at
the generic points of the normalized fibre in Conrad's appendix to
Prasad–Yu, *On quasi-reductive group schemes*, author preprint,
Remark A.7 on printed and PDF p. 30. The registered source is
`prasad-yu-2006-quasi-reductive-author-preprint`, SHA-256
`138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`.
