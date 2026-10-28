# Actual disintegration transfer for the intermediate-tail chart

Worker 318's internal construction specializes the exact published
`LowerBlockQuotientDisintegrationStatement` to the chart and determinant
density used by the intermediate-tail span calculation. The disintegration
proposition remains an explicit premise; this module does not prove it.

The tail rank is `n+1`, the additional lower-block rank is `k+1`, and the full
quotient has JPSS index `n+(k+1)`. The published disintegration statement uses
the equal index `n+1+k`. The proof transports the supplied full quotient
measure to that index and preserves its compatibility with the same normalized
group and unipotent Haar measures. It applies the explicit disintegration
premise, then transports measurability, absolute integrability and complex
integrals back through the actual rank homeomorphism. The transported chart
is the actual `quotientChart`, and the determinant density is exactly
`quotientDensity (normalizedAbsoluteValue T) n (k+1)`.

The conclusion retains the resulting regular, sigma-finite, positive right
Haar measure on the lower-triangular group, its finiteness on compact sets,
and the positive real scalar `C`. It gives both directions of absolute
integrability and the integral formula with factor `C` for every Borel
measurable complex function. The additive rectangular measure is the actual
product measure built from the supplied additive Haar measure. Neither the
scalar nor either independently supplied compatible quotient measure is
discarded.

The provenance is internal equality transport and specialization of the
named published proposition. This proves no new disintegration formula
without that premise and does not establish the closed intermediate-tail
span inclusion.

`DisintegrationData` packages the actual triangular measure, its regularity,
sigma finiteness, positivity, finiteness on compact sets and right invariance,
together with the positive real normalization and the full transfer law.
Its group and quotient measures use the fixed Borel structures, and its
matrix measure uses the product measurable structure on the Borel field.
`disintegrationDataOfStatement` uses classical choice on the proved
conditional existence result to construct this data for every pair of
compatible measures and every supplied additive Haar measure. The
disintegration proposition is a required proof input to the construction;
it is not proved or replaced by the packaged data.
