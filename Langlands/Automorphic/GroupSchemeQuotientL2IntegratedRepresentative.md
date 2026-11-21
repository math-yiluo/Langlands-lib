# Continuous representatives of compactly weighted quotient orbits

Use the canonical Haar measure `μQ` on the Library's positive-central
rational quotient `Q = PositiveRationalQuotient F G T i`, with the same
split-centre and right invariance hypotheses as in
[GroupSchemeQuotientL2Integrated](GroupSchemeQuotientL2Integrated.md).
Write `ρ(a)` for the original quotient right action on `Lp ℂ 2 μQ`.
Let `b : Y → G(𝔸_F)` be continuous, where `Y` is second countable and its
open sets are measurable. The measure `ν` on `Y` is s-finite and finite on
compact sets. Let `w : Y → ℂ` be continuous and compactly supported, and
let `h : Q → ℂ` be continuous and represent `φ : Lp ℂ 2 μQ`.

`weightedQuotientOrbitIntegral` is the continuous function on `Q` given by

\[
q \longmapsto \int_Y w(y)\,h(q\, b(y))\,d\nu(y).
\]

Here `q b(y)` denotes the actual right translation on the homogeneous quotient.
`GroupSchemeQuotientL2IntegratedRepresentativeStatement` asserts that
`y ↦ w(y) • ρ(b(y)) φ` is Bochner integrable, and that its Bochner integral
has the above function as a representative. The second assertion is almost
everywhere equality on `Q` for `μQ`. It is proved by
`groupSchemeQuotientL2IntegratedRepresentative`.

## Implemented proof and provenance

This is a derived comparison lemma for moving between the pointwise
convolution and the Hilbert-space orbit integral, in particular when `b`
is the inclusion of the archimedean factor. The right action on the quotient
is jointly continuous. For the scalar integrand this gives continuity on
`Y × Q`, and the support in `Y` is contained in the fixed compact support of
`w`. Mathlib's `continuousOn_integral_of_compact_support` proves the claimed
continuity on `Q`. The quotient's Borel structure and σ-finite Haar measure
allow the application of the [L² integral comparison](../Analysis/L2BochnerRepresentative.md).
The orbit of `φ` composed with `b` is continuous in `L²`, and the isometry
property bounds the weighted orbit's norm by `‖w(y)‖ * ‖φ‖`; this proves
Bochner integrability. Measure preservation of right translation and the
almost everywhere formula for the representative of an `Lp` scalar
multiple verify the comparison lemma's fibre hypothesis.

This comparison does not produce a continuous representative of an
arbitrary input class `φ`. It transports an existing continuous
representative through the weighted integral. It asserts neither
differential stability nor irreducibility of a cuspidal summand.
