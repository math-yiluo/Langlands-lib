# Actual first-dual rank-one convergence from inverse-transpose matrix data

Worker 396. Internal derived prerequisite for the actual matrix functional-equation
comparison. The field and representation-carrier universes remain independent.

`firstDualModelRepresentationEquiv` gives an actual representation equivalence
from the inverse-transpose pullback of the original coefficient model to the
ordinary model of `inverseTransposePullback sigma` with functional
`firstDualFunctional psi sigma ell`. The target uses the actual standard
character for `psi.scale(-1)`. Its underlying linear map is the published
`firstDualModelEquiv`; the new action check is the group identity

```text
(w * iota(g)) * iota(s) = w * iota(g*s).
```

This retains the actual unsigned long Weyl representative `w`, the actual
inverse-transpose automorphism `iota`, and the actual first dual function.
It refines the existing inverse-character dual model construction to the
`psi.scale(-1)` character used by the functional-equation definitions. It
requires no irreducibility, uniqueness or identification with a smooth
contragredient.

`iotaMatrixAnalyticAssertions_firstDual_iff` first uses the published equality
of the transformed bi-smooth coefficient family with the ordinary coefficient
family of the inverse-transpose pullback. It then transports through the
constructed representation equivalence. Both directions preserve the same
measure, residue variable, polynomial, shifted convergence bound and actual
rational-value family.

`PadicFirstDual.matrixAnalyticAssertions_of_iota` specializes this transfer to
the canonical p-adic topology and normalized group Haar measure. With
smoothness of the original representation, the inverse-transpose pullback
is smooth by the published continuous-pullback theorem, so the published
BoxConvergence results apply to its actual coefficient model.

`rankOne_convergesOnRight_of_iota` obtains one right half-plane on which, for
every original model vector `W` and every right translate `a`, the integral

```text
integral_GL1 firstDualFunction(W)(diag(det g,1,...,1) * a)
             |det g|^(s-(m+1)/2) dg
```

converges absolutely. The bound is common to all `W` and `a`. The proof uses
the actual dual vector `translatedFirstDualModelEquiv psi sigma ell a W`
in the constructed model, whose underlying function is exactly the displayed
first dual translate.

`rankOne_rationalContinuation_of_iota` similarly supplies a convergent
rational continuation of each displayed integral from the same transformed
matrix analytic assertions. The actual right translate, character reversal,
Weyl element, spectral shift and group measure are retained. Neither a new
additive measure nor a Fourier normalization enters these deductions.

These are internal consequences of the published actual dual model maps,
continuous inverse-transpose pullback, bi-smooth coefficient transport and
positive-volume box convergence calculation. No new original-source
transcription is asserted. The conclusions concern the rank-one integral
with zero rectangular rows for the first dual model. They do not establish
the complementary-block dual integral, identify its continuation with a
Fourier partner, or prove the final normalized gamma equation.
