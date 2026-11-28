# Compatible twists to the split centre for arithmetic weak base change

Let `E/F` be an extension of number fields in a common universe with compact additive
adele quotients. Let `S` over `F` and `T` over `E` be cuspidal operator realizations of
the same positive rank, with `T` an arithmetic weak base change of `S`.
`WeakBaseChangeSplitCentreStatement` gives a complex power of the lower idelic absolute value
whose determinant twist of `S`, together with the determinant twist of `T` by its norm
pullback, makes both realizations trivial on their respective split centres. The twisted
classes still satisfy arithmetic weak base change. Their spectral presentation universes
are independent.

`CuspidalSpectralPresentation.isArithmeticWeakBaseChangeOf_heckeDeterminantTwist` first
proves the compatibility for any lower Hecke character and its norm pullback. Outside
a finite set of lower places, both twisted spectra are defined at all places in the
comparison and the lower character is unramified. The determinant twists multiply the
parameters by the character values at the chosen uniformizers. The upper value is the
lower value raised to the residue degree, by `HeckeCharacter.normComp_finiteUniformizerValue`.
`Eigenvalues.power_scale` then preserves the defining Satake relation. The equivalence
`IsoClass.isWeakBaseChangeOf_isoClass_iff` gives the result on actual cuspidal classes.

For `CuspidalOperatorRealization.isTrivialOnSplitCentre_of_isWeakBaseChangeOf`, evaluate the
lower central action at a nonvanishing value of a cusp form. Split-centre triviality implies
that the central character is one on the positive real ideles. The upper central character
is its norm pullback by `hasCentralCharacter_normComp_of_isWeakBaseChangeOf`. The idele norm
sends a positive real idele to the positive real idele with parameter raised to `[E : F]`, by
`AdelicFunctoriality.ideleNorm_positiveRealIdeles`. Evaluating the upper central action thus
gives split-centre triviality upstairs.

`weakBaseChangeSplitCentre` chooses the lower power supplied by
`NormPowerTwist.exists_normPower_twist_isTrivialOnSplitCentre`. It applies the compatibility
and the split-centre implication to the twisted pair.

Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace Formula*
(1989), I.4.2 and III.1, describes the Satake power relation. Proposition III.4.4(ii)
(printed p. 210, PDF p. 224) gives the corresponding norm pullback of central characters.
The simultaneous normalization combines these comparisons with the single-field
normalization in `Langlands.Global.Factors.CuspidalNormPowerTwist`.
