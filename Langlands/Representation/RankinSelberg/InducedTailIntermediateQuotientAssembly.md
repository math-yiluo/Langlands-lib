# Actual quotient-to-span assembly for the intermediate tail

Worker 318 combines the actual quotient comparison with the integral and span
assembly by Worker 829. This internal derivation keeps the diagonal extension,
the full representation's Whittaker type, the test representation's smoothness,
and the lower-block measure transfer as hypotheses.

`continuous_zeroRow_integrand_of_mem` applies the published zero-row continuity
theorem to members of the actual standard and inverse coefficient images. The
membership witnesses supply the functionals and coefficient-model elements
required by that theorem. No functional is selected in the statement.

`mem_full_zetaSpan_of_diagonal_extension` uses the canonical p-adic topology and
absolute value, with their Borel structures. Its full representation has matrix
rank `(n+1)+d+(c0+1)`, its test representation has rank `n+d+1`, and its tail
function has rank `n+1`, where `d=k+1`. It assumes a diagonal extension for every
Schwartz row function and actual inverse test-coefficient membership. The
quotient measures and the two parameter measures remain explicit. The parameter
measures are s-finite, positive on nonempty open sets, and finite on compact
sets. A positive real constant `C` occurs in the assumed integrability
equivalence and integral formula for every Borel measurable complex function
under the actual `quotientChart` and `quotientDensity`.

For the actual reversed-character tail quotient integrand, the theorem assumes
integrability on a right half-plane and rational continuation of its quotient
integrals to `R`. It concludes membership of `R` in the actual full Laurent
span, using the unique zero-row point mass and an explicit numerical equality
transport of the full representation. It does not claim the final
same-character canonical induced-tail span statement.

The proof chooses the compact open localizers and the localized full coefficient
by `exists_localized_quotient_integrand_comparison`. The full coefficient's
actual-image membership and smoothness pass through the numerical rank
transport. Canonical p-adic second countability identifies the matrix product
measurable structure with its Borel structure, so the open localizers are
measurable. The continuity lemma makes its actual quotient integrand Borel
measurable, so the measure-transfer hypothesis applies to this function.
Continuity of the determinant density gives its measurability, and its
definition makes it finite everywhere. The localizers are nonempty subgroups,
so their real volumes are positive. Worker 829's
`mem_zetaSpan_of_localized_disintegration` then gives the result, removing the
nonzero scalar only at the Laurent-span step.

Provenance is the internal composition of the named adapters and the published
zero-row continuity theorem. The motivating calculation is JPSS 1983 section
9.3, printed pages 456–457, already cited in the component modules. This module
does not prove diagonal extension, full Whittaker type, measure disintegration,
or character transport.
