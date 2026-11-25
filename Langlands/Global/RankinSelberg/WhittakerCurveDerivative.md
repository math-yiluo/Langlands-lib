# Lie-curve derivatives of actual global Whittaker integrals

This internal supporting construction for the archimedean functional equation at the real
places (`RealPlaceFunctionalEquationStatement`) is in namespace
`Langlands.Global.RankinSelbergGlobal.WhittakerCurve`. It concerns the existing
global character-coefficient integral, rather than a newly chosen Whittaker
functional. Its compact-quotient dominated-differentiation argument follows
the method already used for iterated torus coefficients in the Library's
`Langlands.Automorphic.CuspidalWhittaker.CurveDerivative`.

For a real direction `X` in the full archimedean Lie algebra,
`adelicOneParameter F n X s` is the genuine adelic point whose infinite
component is `infiniteOneParameter F n X s` and whose finite component is
identity, transported through `GeneralLinearGroupPoints.adelicEquiv`.
`continuous_adelicOneParameter` proves continuity of this curve.

Let `F` be a number field with compact adele quotient, `T` an actual cuspidal
operator realization of `GL_(r+1)`, and `χ` a standard additive character of
the adeles. For every actual vector `x`, adelic group point `g`, real
archimedean Lie direction `X` and real `t`,
`cuspWhittaker_hasDerivAt` proves that

```text
s ↦ cuspWhittaker F T χ x (g * adelicOneParameter F (r+1) X s)
```

has derivative

```text
cuspWhittaker F T χ (T.realization.lieOperator X x)
  (g * adelicOneParameter F (r+1) X t)
```

at `t`. Here `lieOperator` is the existing action of the real Lie generator
inside the full enveloping algebra. The theorem includes every real
direction of the full archimedean group, and hence directions supported at
either a real or a complex place.

The proof first rewrites the realized cusp function as evaluation of the
same actual continuous rational-invariant function. The Library theorem
`OperatorRealization.hasDerivAt_evaluate_oneParameter` then proves the
pointwise derivative formula for that function.

For the integral, the module supplies a general lemma
`hasDerivAt_integral_out`. The integration space is a compact left quotient
of a topological group, with a finite Borel measure. Both integrands descend
from invariant functions on the group. `continuous_out_family` proves joint
continuity on the parameter times the quotient through the open quotient
map; it does not require the representative function `Quotient.out` to be
continuous. Joint continuity bounds the derivative integrand uniformly on
`closedBall t 1 × quotient`. This constant bound is integrable for the finite
measure, so Mathlib's dominated differentiation theorem applies.

For the actual Whittaker integral, rational invariance of the realized form
and of the generic character supplies descent. Continuity of the form, the
adelic curve and the generic character supplies joint continuity.
Compactness of the unipotent rational quotient and the existing normalized
probability measure supply the integration hypotheses. Multiplying the
pointwise derivative by the fixed conjugate generic character gives the
derivative integrand. Unfolding the existing Whittaker definitions identifies
the two integrals with the asserted actual coefficients.

This proves differentiation along exponential curves. It does not
assert smoothness of the restriction, a polynomial growth bound, or the
matrix-model `mfderiv` identity in `RealPlaceWhittakerAnalyticStatement`.
Those require further arguments. No functional equation is proved here.
