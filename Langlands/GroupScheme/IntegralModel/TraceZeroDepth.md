# Integral depth models for the actual quadratic trace-zero line

For a separable quadratic extension `L/k`, choose a nonzero trace-zero scalar
`eta`. Let `v` be a surjective integer-normalized multiplicative valuation of
`k`, with Henselian valuation ring, and let `R` be that valuation subring.
The real number `traceZeroOffset` is the finite prolonged additive value of
`eta`, using the existing Henselian invariant prolongation.

`traceZeroRationalSectionsEquiv` evaluates the relative sections of the identity
rational test through the canonical global-sections isomorphism.
`traceZeroRationalTensorEquiv` tensors this with the identity on `L` and then
contracts `k ⊗[k] L` to `L`. It intertwines the actual conjugations.
Thus `traceZeroRationalParameter` takes a rational point to its actual field
trace-zero coordinate, rather than assigning an independent coordinate model.
The tensor parametrization proves that this field coordinate is the scalar
coordinate of the actual additive-line isomorphism multiplied by `eta`.

The prolongations on `k` and `L` agree on every base scalar by their common
integer logarithm formula, including zero. Additivity on products then proves
that the field-value bound at depth `r` is exactly the scalar-value bound at
`r - traceZeroOffset`. The zero scalar is included with value infinity.

`traceZeroDepthModel` transports the coordinate-depth polynomial integral line
at this shifted depth through `traceZeroVectorIso`. The resulting model is
smooth with geometrically connected fibres. Its integral-point image is
exactly the points whose actual field trace-zero coordinates have additive
value at least `r`, for every real depth. For `r ≤ s`, the explicit integral
transition extends the generic identity. Every compatible identity extension
has smooth, connected and unipotent scheme-theoretic special-fibre kernel,
by the transported diagonal-vector kernel result and generic rigidity.

This is an internal derivation of the construction in Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Section C.3 and Fact C.3.1,
printed page 698 (PDF page 729), using the normalized valuation conventions
of the Library. It uses the actual tensor trace-kernel representation from
`SU3TraceZeroScheme` and the explicit coordinate-depth models. It does not
identify this group with an arbitrary supplied relative root subgroup or
establish that a supplied apartment filtration has these depth subgroups.
