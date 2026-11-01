# Actual fixed-slice absolute convergence and first unfolding

This module proves the unchanged published proposition
`Langlands.RankinSelberg.TwoBlockFixedSliceUnfoldingStatement.{uF,uV,uW}` by the
exact theorem `Langlands.RankinSelberg.twoBlockFixedSliceUnfolding`.

The source is Jacquet–Piatetski-Shapiro–Shalika, *Rankin–Selberg convolutions*
(1983), Section 4.6, printed pages 410–412, especially equation (4) and the first
integral on page 412. Source ID `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The source justifies the first unfolding using compact support modulo the full
unipotent subgroup on each determinant slice. The proof here supplies the
local boundedness and quotient-measure details needed to implement that argument.

The proof reuses the published ordinary Jacquet convergence assembly. Its bound
is chosen after the block representations and their supplied inverse-character
functionals, before the twist parameter, section, test representation, coefficient,
row function, or slice. This assembly also permits zero functionals. The published
fiber formula then gives absolute integrability on every rectangular fiber.
The published representative identity identifies the signed radical average with
`W(g) J(f)(g) Φ(lastRow g)`.

The continuity helper `TwoBlockFixedSliceAnalysis` uses an open right stabilizer
of the smooth section to make the entire raw rectangular integrand locally
constant in the group argument. Postcomposition with integration preserves local
constancy. Actual test coefficients are continuous for every smooth test
representation, and the row function is continuous. The actual integrand and both
radical averages therefore are continuous and measurable. This argument does not
need a common right stabilizer for the row function or a parameter-dependent
dominating function.

The absolute average vanishes whenever the product of the test coefficient norm
and the row function norm vanishes. Its support on the clopen determinant slice
is thus contained in that of the published compactly supported row norm product.
The slice indicator of the absolute average is continuous and has compact support.
Every compatible quotient measure is regular and finite on compact sets, so this
function is integrable. This is the local boundedness step beyond pointwise
convergence and compact support alone.

Finally, the published two-block quotient integration theorem supplies compatible
quotient measures, right-invariance certificates, the positive finite cube mass,
and the radical fiber kernel. Each kernel fiber integral is transferred from its
rectangular pushforward. The kernel norm integral is the real part of the absolute
radical average, using the compatibility of the real embedding with the Bochner
integral. The tower's restricted integrability criterion proves integrability of
the actual integrand on the inverse-image slice. Its Bochner law then proves
integrability of the signed average and the required equality of integrals.

The supplied self-dual rectangular Haar is unchanged. The factor `c` is its mass
on matrices with integral entries, positive and finite by the quotient tower;
the identity has the direction
`integral A = c.toReal • integral E`. No mass-one assumption is made. The field,
test-carrier and block-carrier universes stay independent, the twists are exactly
`(-u,+u)`, reducible Whittaker-type blocks and zero functionals are included, and
the test coefficient is the actual image of any smooth representation. The proof
does not use Section 7 or any gamma or L factor multiplicativity statement.
