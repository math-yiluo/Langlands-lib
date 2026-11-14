# Actual unipotent radicals after unramified extension

This internal construction uses the published special-fibre quotient data and
actual maximal-unramified extension of a nonarchimedean local field at arbitrary
universe `u`. It introduces no new original-literature assertion.

`IntegralModel.unramifiedSpecialFibreIso` compares the actual special fibre of
`M.baseChangeUnramified` with the scalar extension of `M.specialFibre` along
`residueToFixedField`. It uses the same commuting square and comparison as the
published `unramifiedSpecialFibreMap`. The equality
`unramifiedSpecialFibreMap_eq` records this precise compatibility.

`SpecialFibreQuotientData.exists_unramifiedRadical` assumes the supplied
`Q.IsReductiveQuotient`. It produces a group and an actual inclusion into
`D.neutral.baseChangeUnramified.specialFibre` that is an unipotent radical in the
Library's greatest smooth connected normal unipotent closed-subgroup sense.
It also identifies `Q.unramifiedKernelPoints` with the generic image of the
integral sections whose reductions lie in the rational-point range of that
inclusion. The image and inverse-image maps are the published reduction and
integral-point homomorphisms of the actual upstairs model.

The proof extends the supplied radical along the actual residue-field map,
then transports it through the inverse comparison isomorphism. The published
`fixedFieldResidueIsAlgClosure` makes this residue extension algebraic; finiteness
of the original residue field makes it separable. Smoothness and affineness of
the original special fibre follow by pullback from the supplied neutral model,
and connectedness follows from its supplied connected fibres. Thus the
published separable radical base-change theorem applies. The represented fppf
quotient condition also survives base change. Its all-test kernel equality,
specialized to the residue-field point scheme and transported through the same
isomorphism, gives the equality of point subgroups. The supporting generic
lemma `GroupScheme.rationalPoints_kernel_iso` implements this transport by
rewriting the represented subgroup range through the ambient isomorphism. Taking the reduction
preimage and generic-point image completes the subgroup identification.

No reduction-surjectivity or root-generation assertion is made here; those are
separate obligations for consumers.
