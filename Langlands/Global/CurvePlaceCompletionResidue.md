# Completion and the actual curve-place residue field

For fields `k` and `F` in one arbitrary universe, a `k`-algebra structure on
`F`, and an actual `AlgebraicCurve.Place k F` named `v`, this module constructs

```text
curvePlaceCompletionResidueEquiv v :
  v.ResidueField ≃+* IsLocalRing.ResidueField (curvePlaceCompletionIntegers v).
```

Here the original ring is `v.toValuationSubring`, its residue field is the
existing quotient by its maximal ideal, and the completed ring is the actual
valuation subring of `v.heightOneSpectrum.adicCompletion F`. These are the
published `curvePlaceCompletion` and `curvePlaceCompletionIntegers` objects,
with their existing adic valuation and completion topology. No auxiliary field,
chosen residue isomorphism, or supplied approximation hypothesis is used.
There is no function-field, perfectness, separability, finite constant-field,
or finite residue-field assumption.

`curvePlaceIntegersMap` is the existing algebra map from the original valuation
ring into the completed valuation ring. `curvePlaceIntegersMap_coe` records that
its underlying completed-field element is the image of the original field
element. `curvePlaceCompletion_mem_maximalIdeal_iff` identifies membership in
the completed maximal ideal with completed valuation strictly less than one.

Composing the integer map with reduction defines
`curvePlaceCompletionResidueMap`. The adic valuation formula on original field
elements and the original height-one-prime valuation criterion show that this
map vanishes precisely on the original maximal ideal. This is recorded by
`curvePlaceCompletionResidueMap_eq_zero_iff` and the kernel equality
`curvePlaceCompletionResidueMap_ker`.

For a completed integer `x`, density of the original field in its completion
provides `b` such that the valuation of `b - x` is less than one. The
ultrametric inequality, together with the integrality of `x`, bounds the
valuation of `b` by one. The published
`curvePlaceCompletion_mem_integers_iff` then puts `b` in the original valuation
ring. The resulting statement is `curvePlace_exists_integer_sub_lt_one`.
Every completed residue class has a completed integer representative, so this
approximation proves `curvePlaceCompletionResidueMap_surjective`.

The first isomorphism theorem and the kernel equality give the displayed
canonical ring equivalence. `curvePlaceCompletionResidueEquiv_residue` specifies
it on every original integer: reduce the integer, apply the equivalence, and
obtain the same class as first embedding the integer in the completed ring and
then reducing. This formula fixes the comparison map explicitly.

This is derived implementation infrastructure for the actual function-field
local-compactness branch of the Conrad program. Its proof uses the published
curve-place completion, Mathlib's density and valuation theorems, and the ideal
quotient equivalence. It is not a numbered assertion transcribed from Conrad.
It asserts a ring equivalence and the stated approximation and reduction laws;
it does not assert residue finiteness, local compactness, diagonal discreteness,
or completion of the whole-paper program.
