# Hilbert transport of actual CM argument pullback

Let `K : Type uK` be any number field with `NumberField.IsCMField K`, let
`n : ℕ`, let `S : OperatorRealization K n`, and supply `b : S.UnitaryForm`.
The construction includes rank zero. Coefficients are complex.
`completedComplexConjEquiv` extends the actual complex-linear equivalence
`S.complexConjEquiv` to a surjective complex-linear isometry of the chosen
positive-form Hilbert completions:

`b.finiteForm.HilbertCompletion ≃ₗᵢ[ℂ] b.complexConj.finiteForm.HilbertCompletion`.

The implemented source form is
`a = b.finiteForm.comp (CMConjugation.finiteConj K n).toMonoidHom`.
Its positive core, completion and canonical embedding are exactly those of
`b.finiteForm`. The actual equivalence
`e = S.complexConjFiniteEquiv` identifies this precomposed finite representation
with the finite action on the genuine CM image of the original function
subspace. The generic constructor `a.completedOfEquiv e` transports the form
through `e.symm` and completes the original equivalence. The target form
`a.ofEquiv e.symm` is definitionally the finite form of the published
`b.complexConj`. Thus the constructor supplies the extension without an
additional form-preservation or surjectivity assumption.

Write `E = b.completedComplexConjEquiv`, `j = b.finiteForm.toHilbert`, and
`j' = b.complexConj.finiteForm.toHilbert`. The generic laws
`completedOfEquiv_toHilbert` and `completedOfEquiv_symm_toHilbert`, applied to
`a`, `e`, give

`E (j f) = j' (S.complexConjEquiv f)`

and

`E.symm (j' f') = j (S.complexConjEquiv.symm f')`.

On original embedded vectors the represented functions therefore evaluate at
the arithmetic CM-conjugated adelic argument, by the published
`S.evaluate_complexConjEquiv`. Complex scalar values are fixed throughout
this construction.

The generic `comp_completedOfEquiv_completedOperator` gives, for every
`g : FiniteAdelicGL K n` and completed vector `x`,

`E (b.finiteForm.completedOperator (CMConjugation.finiteConj K n g) x) =`
`  b.complexConj.finiteForm.completedOperator g (E x)`.

Equivalently this follows from `comp_completedOperator` and
`completedOfEquiv_completedOperator` in sequence. The target and source compact
forms have the same respective positive cores as their finite forms. Apply
`completedOfEquiv_covariant` to the actual compact operators and their
`completedOperator_toHilbert` identities, with algebraic covariance
`(S.complexConjEquiv_compact k f).symm`. It gives, on these same completions,

`E (b.compactForm.completedOperator (CMConjugation.compactConj K n k) x) =`
`  b.complexConj.compactForm.completedOperator k (E x)`.

These are specializations of the generic laws in
`Langlands.Representation.Unitary.CompletionOperations`; this module keeps the
actual constructor as the sole new declaration. All completed operators used in
the compact specialization already exist and are continuous.

This is an internal derivation from `OperatorCMUnitaryForm`,
`OperatorCMFiniteComparison`, the actual function transport in
`OperatorCMTransport`, and the published Hilbert completion transport. No new
original-literature identification is claimed. The chosen original positive
form is explicit; its existence, spectral occurrence, extension of unbounded
differential operators and full archimedean globalization remain separate.
