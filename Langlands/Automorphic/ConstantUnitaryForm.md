# A positive form on the actual constant automorphic realization

This internal construction supplies an explicit positive definite Hermitian
form on `ConstantFunctions.realization F n`, for any number field in an
arbitrary universe and every natural matrix rank. Coefficients are complex.
The carrier remains the actual embedded line of constant automorphic forms.

`ConstantFunctions.unitaryForm F n` pulls the usual scalar inner product
back through the inverse of the published scalar equivalence. Its formula is

```text
B(f,g) = scalar(g) * conjugate(scalar(f)),
```

where `scalar(f)` is evaluation of the represented function at the identity.
The private scalar form uses Mathlib's existing complex inner product, and
the published injective pullback supplies the positive Hermitian core and
finite invariance. The finite equivariance is the previously proved trivial
finite action on the actual constant line.

The compact action also fixes each constant vector. The theorem
`realGenerator_eq_zero` applies the actual enveloping action formula on
constants: the augmentation kills the enveloping generator of each
complexified real Lie direction. Thus the actual real differential is zero,
and the same positive form satisfies its required skew equation.

`unitaryForm_inner` identifies the form in scalar coordinates.
`unitaryForm_inner_scalarEquiv` gives the displayed scalar product, and
`unitaryForm_inner_evaluate` expresses it directly through evaluations of
the original represented functions. The remaining results supply the
actual whole-operator unitarizability witness, its descended class predicate
and generic unitarizability on the actual finite form image.

All construction obligations are internal consequences of the published
constant-line scalar equivalence and action formulas, the positive-form
pullback and the actual operator-form interface. Mathlib supplies the usual
complex inner product. No new original-literature identification is made.
There is no compactness hypothesis on an adele quotient. This algebraic form
does not assert a Hilbert globalization, continuity of the form for a function
space topology, an invariant integral formula or a spectral occurrence result.
