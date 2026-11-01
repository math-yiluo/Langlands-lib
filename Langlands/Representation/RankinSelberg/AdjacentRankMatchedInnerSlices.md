# Matched original and transformed inner slices

This derived prerequisite lifts the same-family compact-average identities to actual inner
determinant-slice integrals. Its intended use is JPSS Section 6.3, printed
pp.434–437, with a square test and its reflected Fourier transform.

The two tests and two quasicharacters are fixed before choosing the finite
family. Intersect the published compact open invariant subgroups of the two
tests and characters. This common subgroup is still compact open and stable
under inverse transpose. The same-family compact-average theorem supplies one
family of original model vectors and one family of actual bi-smooth matrix
coefficients for both computations.

The determinant-slice weights are compactly supported and continuous on the
actual group. Original and dual coefficients, as well as the original and
inverse-transpose matrix functions, are continuous. All slice integrands are
therefore genuinely integrable for the unchanged normalized group Haar.
Left averaging preserves each weight. Applying the published averaging
integral identity and the same finite expansion proves both integral
formulas, retaining exactly `dualModelLinearMap B` and `coefficientIota f`.

Global convergence, rational continuation, the outer quotient calculation,
the dual finite zeta-product formula and parent gamma/L targets remain open.

`adjacentRankDualInnerSliceIntegral` is the literal integral of the second
slice weight multiplied by `dualFunction W (g*h)`. Both weights use the same
canonical determinant order, normalized absolute value, integer slice `j`,
complex exponent `s`, and general-linear Haar. `PhiD` and `chiD` are arbitrary
fixed second inputs, so one may specialize them to the reflected Fourier
test and inverse character without proving a separate invariance law for
that transform.

`adjacentRankInnerSlice_matchedFiniteSeparation` chooses `N` and the family
`B` before the input vector `W`, then actual bi-smooth model coefficients `f`
before every `j`, `s` and external `g`. Its conclusions give integrability of
the original and dual model integrands, integrability of every original
and transformed matrix summand, and both finite integral identities. The
transformed vectors are exactly `dualModelLinearMap B`; the transformed
matrix functions are exactly `coefficientIota f`, for the same finite index
set. The hypotheses require admissibility and a specified standard Whittaker
functional, which may be zero. Reducible representations, independent
original-carrier universes and actual rank one are included; the original
carrier is given no topology.

The private scalar averaging argument reuses `leftAverage_integral` and the
nonzero normalized Haar mass of the compact open subgroup. It moves the
inverse mass outside the integral, cancels it against the averaging mass,
substitutes the finite compact-average expansion, and integrates the finite
sum using the integrability conclusions already established. This is the
same averaging argument on each side, with one common subgroup and one
choice of the finite model family.

The original is Jacquet–Piatetski-Shapiro–Shalika, *Rankin–Selberg Convolutions*
(1983), Section 6.3, printed pp.434–437, especially formula (7) and the
transformed compact-average identity before (14). It is registered as
`jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Intersecting the two invariant compact open subgroups is an internal
formalization choice that supports arbitrary fixed second tests; it
preserves the uniform finite choices required by the source calculation.
No Fourier relation between the two tests or characters is assumed in
this intermediate result, and no parent multiplicativity theorem is used.
