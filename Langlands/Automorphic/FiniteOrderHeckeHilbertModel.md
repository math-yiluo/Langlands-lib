# The scalar Hilbert model of actual finite-order Hecke lines

For a supplied finite-order continuous complex Hecke character `χ` on the
actual idele-class group of a number field `F : Type uF`, and any natural
matrix rank `n`, `FiniteOrderHeckeRealization.hilbertScalarEquiv` constructs
a complex-linear isometric equivalence from the actual Hilbert completion
of the chosen finite invariant form on the actual automorphic character
line to the usual complete complex Hilbert space `ℂ`.

The source is exactly
`(unitaryForm F n χ hχ).finiteForm.HilbertCompletion`. Its positive form
was constructed by actual determinant multiplication from the constant-line
form. Its algebraic carrier is the existing embedded line of functions
`g ↦ χ(det g) * c`. The target is the ordinary normed complex field.
There is no additional complete-model or positive-form existence hypothesis.

The constructor applies
`InvariantPositiveForm.completeModelEquiv` with the inverse of the published
`scalarEquiv` as its model map. The published `unitaryForm_inner` proves
the exact inner-product identity required by that generic construction.
Completeness of `ℂ` supplies the last instance.

The extension laws remain in the generic complete-model API, so they can
be specialized without introducing another collection of concrete wrappers.
With `b = (unitaryForm F n χ hχ).finiteForm`,
`e = (scalarEquiv F n χ hχ).symm` and
`he f g = (unitaryForm_inner F n χ hχ f g).symm`, they give

```text
hilbertScalarEquiv (b.toHilbert f) = (scalarEquiv ...).symm f = f(1),
hilbertScalarEquiv.symm c = b.toHilbert (scalarEquiv ... c).
```

Here `f(1)` means evaluation of the original represented continuous function
at the identity full adelic matrix; `scalarEquiv_symm_apply` identifies it
with the inverse coordinate. The equivalence therefore sends the embedded
vector `scalarEquiv ... 1` to `1`, and its inverse gives a concrete nonzero
completed vector. It preserves norms and inner products in both directions
and is uniquely determined among continuous linear extensions by the first
formula. `toHilbert_surjective_of_completeModel` also says the canonical
embedding of this actual line is surjective.

For the finite group, specialize
`completeModelEquiv_completedOperator` to
`D = z • ContinuousLinearMap.id ℂ ℂ`, where
`z = (χ.adelicDeterminant n (AdelicGL.ofFinite F n d) : ℂ)`.
The original coordinate covariance follows from
`finiteRepresentation_scalarEquiv` and surjectivity of `scalarEquiv`.
Thus the completed finite operator acts in scalar coordinates by `z`.
For the standard infinite compact action, specialize
`completeModelEquiv_covariant` to its original operator and
`(unitaryForm F n χ hχ).compactForm.completedOperator`; the finite and compact forms have the
same positive core, hence the same completion and canonical embedding.
Use `compactRepresentation_scalarEquiv` and the scalar obtained from
`AdelicGL.ofInfinite F n k.val`. The resulting equation holds for every
completed vector. These are applications of the generic laws, not additional
definitions of the actual actions.

This is an internal construction from the published actual character line,
chosen positive form and coordinate identity, and the generic complete-model
construction described in its paired Markdown. No new original-literature
identification is used. The construction needs no additive adele-quotient
compactness input and includes rank zero. It asserts no invariant-integral
formula, spectral occurrence, general automorphic factorization, full
infinite-group globalization or recovery of smooth vectors for general
automorphic representations.
