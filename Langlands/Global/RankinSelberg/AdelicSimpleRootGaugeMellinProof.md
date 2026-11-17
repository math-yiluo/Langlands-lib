# Padded Mellin convergence for adelic simple-root gauges

The theorem `adelicSimpleRootGaugeMellin` proves the unchanged published
`AdelicSimpleRootGaugeMellinStatement`. The proof uses actual adelic points,
the published upper-left padding map, and the defined Whittaker quotient
measure.

For a gauge of exponent τ and a proper block of size t + 1, set

    T = τ + 3 + ∑ (j + 1)(t − j),    0 ≤ j ≤ t.

The proof takes the common nonnegative threshold C = max(0, T) before
quantifying over the gauge. The imported padded torus estimate proves
finiteness of the gauge times the determinant weight and the inverse
actual diagonal conjugation modulus whenever σ > T.

Apply the single-torus quotient criterion to
`f(g) = Ξ(pad(g)) · ofReal(detNorm(g)^σ)`. Padding is continuous, so this
kernel is measurable. Padding preserves upper unipotent and standard
compact elements. The gauge's invariances, determinant norm one on
unipotent elements and standard compact elements, and multiplicativity
of the determinant norm give both invariances required by the criterion.
The inverse-modulus torus estimate then proves finiteness for the actual
Whittaker measure.

This proof is internal derived content: the analytic input is the imported
Schwartz–Bruhat Mellin estimate in block-root coordinates; the quotient
step uses compact Iwasawa parameters, Haar translation, and the published
compact-uniform quotient criterion. No new analytic hypothesis is added
to the target statement.
