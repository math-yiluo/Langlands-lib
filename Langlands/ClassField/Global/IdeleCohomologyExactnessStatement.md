# Image–kernel exactness for principal-idele cohomology

Author: Worker 21.

This module states the proposition
`Langlands.ClassField.Global.IdeleCohomologyExactness.{u}`.
For fields `F E : Type u`, a number-field structure on `E`, an algebra
structure `F → E`, and every natural degree `n`, it asserts

```text
range (Hⁿ(Aut_F(E), Eˣ) → Hⁿ(Aut_F(E), J_E))
  = ker (Hⁿ(Aut_F(E), J_E) → Hⁿ(Aut_F(E), C_E)).
```

The arrows are exactly the published `principalIdeleCohomologyMap F E n`
and `ideleQuotientCohomologyMap F E n`. Their linear ranges and kernels
are submodules of the actual ordinary idele cohomology group.
The coefficient ring is the published lifted integer ring
`NormalizedTwoCocycle.CoefficientScalars.{u}`. The three coefficient
representations use `Additive Eˣ`, the full idele group, and its quotient
by principal ideles, with the published arithmetic automorphism actions.
The additive wrappers preserve the multiplicative groups.

The common universe `u` is arbitrary. No normality assumption is made:
the acting group is explicitly the group of `F`-automorphisms of `E`.
There is no additional number-field instance required on `F`. Degree zero
is included. In degree two, the assertion says that an idele cohomology
class has zero image in idele-class cohomology exactly when it is the image
of a field-unit cohomology class.

This module defines a proposition and does not prove it. It asserts
exactness only at the middle cohomology group. It asserts neither
injectivity of the first arrow nor surjectivity of the second.
It contains no local-to-global injectivity, reciprocity, vanishing,
invariant, or cardinality assertion.

## Provenance

This is an internal specialization of the ordinary group-cohomology long
exact sequence to the published actual coefficient sequence
[`IdeleCoefficientSequence`](IdeleCoefficientSequence.md).
That module proves `ideleCoefficientSequence_shortExact` for the same
parameters and constructs both induced cohomology maps.
Mathlib's `groupCohomology.mapShortComplex₂_exact` in
`Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence`
states exactness of the three consecutive cohomology terms arising from
any short exact coefficient sequence.
`ShortComplex.Exact.moduleCat_range_eq_ker` expresses such exactness as
the range–kernel equality used here. These declarations explain the
proposed derivation and its all-degree scope; this module introduces
no additional arithmetic hypothesis or source claim.
