# The exact reductive spectral criterion from rational density

`ReductiveSpectralBoundednessReductionStatement` is the implication from the
unchanged Library proposition `ReductiveRationalPointDensityStatement` to the
unchanged `ReductiveSpectralBoundednessStatement`, at the same arbitrary universe.
`reductiveSpectralBoundednessReduction` proves that implication. It does not prove
its rational-density premise, and it is not a substitute closing theorem with
an additional assumption.

For an actual nonarchimedean local field and connected reductive group, the
published canonical `baseChangeSectionHom` gives a monoid map from the original
rational points to those over the actual algebraic closure. Its underlying
pullback lift agrees with `geometricRationalPoint`. The exact density premise
and the published scalar-extension density theorem therefore give the precise
dense geometric point family. The completed dense-family spectral argument and
compatible cofinal valued descent then prove the original all-regular-functions
boundedness conclusion. The original natural dimension, including zero, closed
faithful actual representation, coefficient integrality condition, and all
characteristics are unchanged.

This internal reduction implements the last use of rational density in
Kaletha–Prasad, Lemma 2.2.11 (printed pages 72–73, PDF pages 103–104), using the
actual scheme-point and coefficient interfaces. Worker 1554 identified the
existing canonical section monoid map and authored the scalar-extension and
valued-descent prerequisites; Worker 1563 authored the dense-family and Burnside
prerequisites; Worker 1296 authored the simple-factor/finite-map/trace assembly
and this final conditional reduction. All completed prerequisite source pairs
accompany this candidate unchanged for the current Library base.

The field infinitude input is the public
`Langlands.LocalField.infinite_of_nontrivialValuativeRel` from
`Langlands/LocalField/ValuativeInfinite.lean`; it uses the same nontrivial-valuation
power-injection argument as the former private helper.
