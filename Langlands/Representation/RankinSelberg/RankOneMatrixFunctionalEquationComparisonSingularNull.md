# Singular matrices and additive Haar measure

This internal, derived prerequisite supplies the measure identity needed to
pass between full additive matrix integrals and determinant-weighted GL
integrals in the matrix functional equation comparison. It claims no gamma
factor comparison or functional equation.

For a field `K`, `singularLocus r` is precisely the determinant-zero subset of
`Matrix (Fin r) (Fin r) K`. No topology or measure is needed for this definition
or for `finite_singular_scalar_translates`. The latter says that for every
fixed matrix `X`, the scalars `t` for which `scalar t + X` is singular form a
finite set. The proof identifies their determinant with the evaluation of
`(-X).charpoly`, using `Matrix.eval_charpoly`. This characteristic polynomial
is monic and hence nonzero, so Mathlib's finite-root theorem applies. This
also covers `r = 0`, when the determinant and characteristic polynomial are
both one and the root set is empty.

The general theorem `ae_det_ne_zero_of_addInvariant` assumes a Hausdorff,
second countable topological field with continuous ring operations and its
Borel measurable structure. The scalar measure `ν` is s-finite, nonzero and
atomless (`NullSingletonClass`), and the measure `μ` on the square matrix
space is s-finite and invariant under left additive translation. It concludes
that `X.det ≠ 0` for `μ`-almost every matrix. Neither measure is required to
have a chosen Haar normalization.

For every matrix `X`, the finite-root theorem and atomlessness give scalar
almost everywhere nonsingularity of `scalar t + X`. The determinant of this
matrix depends continuously on `(X,t)`, by continuity of the individual
matrix entries and determinant. Its nonzero locus is therefore measurable.
`Measure.ae_ae_comm` exchanges the almost everywhere quantifiers, with the
stated s-finiteness hypotheses. Since the scalar measure is nonzero, some
`t` satisfies matrix almost everywhere nonsingularity. Finally
`eventually_add_left_iff` removes translation by `scalar t` using additive
invariance of `μ`. This proves a genuine almost everywhere statement in the
full matrix space; no support restriction or inference from an averaged
Bochner integral is used.

The canonical p-adic specialization installs the topology, valuation,
Hausdorff, countability and sigma compactness structures from the published
`F.canonicalTopologicalData`. Its punctured neighborhoods of zero are
nonempty by `NormedField.nhdsNE_neBot` for the published explicit spectral
`F.canonicalNormedField`; the two topologies are definitionally equal.
Consequently Mathlib's additive Haar atomlessness instance applies to the
supplied `ν.measure`. Its additive Haar structure also makes it nonzero and,
using sigma compactness, sigma finite. The published `rectangularMeasure`
is exactly the iterated finite product of this same supplied measure. Its
published instances make it sigma finite and additive Haar, so the general
theorem applies without changing normalization.

The resulting declarations are:

- `rectangularMeasure_ae_det_ne_zero F ν r`: almost every square matrix has
  nonzero determinant for the exact measure `rectangularMeasure ν r r`.
- `rectangularMeasure_singularLocus F ν r`: that measure assigns zero to
  `singularLocus r`.
- `rectangularMeasure_restrict_generalLinear F ν r`: restricting that measure
  to the range of the actual map `Units.val : GeneralLinear r F.Carrier →
  Matrix (Fin r) (Fin r) F.Carrier` gives the full measure back. The proof
  uses `Matrix.isUnit_iff_isUnit_det` and the field characterization of units
  as nonzero elements to turn almost everywhere nonzero determinant into
  almost everywhere membership in this range, then applies
  `Measure.restrict_eq_self_of_ae_mem`.

All sizes, including zero, are allowed. There is no Fourier normalization,
self-duality premise, representation hypothesis, or test-function support
premise in these results. In particular, full-measure restriction removal
does not rely on the false claim that box support forces a test function to
vanish on singular matrices.

The provenance is entirely internal: the published GLDensity module imports
the canonical local-field and actual matrix-measure infrastructure; the only
new mathematical argument is the characteristic-polynomial/Fubini/translation
argument above. The implementation uses Mathlib's characteristic polynomial
monicity and evaluation, finite polynomial root set, atomless finite-set
measure, measurable Fubini and additive translation invariance. No original
literature theorem is asserted or cited for this auxiliary result.
