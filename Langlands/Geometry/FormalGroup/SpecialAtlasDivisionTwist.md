# Arbitrary division-unit twists of special formal atlases

Let `C` be the actual embedded integer subring in the special tangent
condition. It is finite étale over `𝒪[K]`, and its local ring is Henselian.
Inverse conjugation by any division unit induces an endomorphism of the
finite division-algebra residue field over the base residue field.
The actual residue field of `C` embeds in this field and is finite.
Normality over the base residue field gives the restriction of conjugation
as an automorphism of the residue field of `C`.

The Henselian finite étale lift gives an actual `𝒪[K]`-algebra automorphism
`β` of `C`. The conjugated embedding and the original embedding precomposed
with `β` now agree in the division-algebra residue field. The étale
intertwiner gives their exact conjugacy by an integer-order unit. This proves
`ConjugationSubfieldFactorization` for every division unit and the given
embedded order.

`twistDivisionUnit` therefore constructs the special coordinate module or
atlas with the inverse-conjugated order action. It retains the underlying
formal laws and scalar-kernel height certificates, commutes with their
coefficient extension, and gives the previous special atlas twist on
integer-order units. `twistDivisionUnitQuasiIsogeny` is the existing map
between the actual order actions in the whole rational atlas tensor.

This implements the special target twist in Drinfel'd, *Coverings of
p-adic symmetric regions* (1976), §2 A, printed p. 109. The height of the
framing quasi-isogeny and its Frobenius correction require further results.
