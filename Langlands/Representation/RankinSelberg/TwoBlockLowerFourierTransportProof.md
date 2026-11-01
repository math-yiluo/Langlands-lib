# Actual lower quotient Fourier and coefficient transport

The theorem proves the published closed proposition
`Langlands.RankinSelberg.TwoBlockLowerFourierTransportStatement` at its independent
field and representation universes. The geometric witness is `lowerDuality`,
chosen before all analytic data. The inverse-character test is `firstDualFunction`,
chosen before the additive measure. Both use the exact representative
`g ↦ weylLong * inverseTranspose g`.

The proof imports the separately paired geometry, supplied-measure and Fourier
helpers. It uses the scalar-section premise exactly as stated. Multiplication of
the rotation, scalar-section and partial-Fourier identities proves the group
integrand comparison. Quotient induction, the representative determinant order
and the canonical normalized absolute value prove the descended comparison.
On slice `k`, the factor becomes the positive real number `q^(-k)`.
The exact restricted measure law gives a measure preserving measurable
equivalence between slices `k` and `-k`. The abstract `scalar_transport` lemma
then proves actual integrability equivalence and the complex coefficient and
real norm integral formulas for total Bochner integrals, with no integrability
premise.

The quotient measure is exactly the transport of every supplied compatible
standard measure for the published `generalLinearHaar` and `unipotentHaar`.
The supplied right invariance certificate is retained. Neither a new measure
normalization nor a duality-invariance premise is introduced. The additive
measure is the supplied self-dual measure for the actual row Fourier pair.
The theorem retains every prime, canonical p-adic field, both positive block
sizes including size one, arbitrary dependent representations and inverse
functionals, and exactly `secondDualFunctional` in the reversed family.
Zero functionals are allowed. Actual dual-section construction remains the
explicit conditional scalar premise.

The original mathematical comparison is Jacquet–Piatetski-Shapiro–Shalika,
*Rankin–Selberg Convolutions* (1983), registered source
`jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`,
Section 4.8(2)–(4), printed p.415, with the actual lower subgroup, block rotation
and rows of Section 4.7(1), pp.412–414. The uniform homeomorphism, measure and
slice formulation is derived packaging. Section 4.7 has equations (1)–(5);
the separate first-block integration (8) is Section 4.9, p.418.

This proof does not use unrestricted multiplicativity, finite-block parents,
Section 7 or Section 9.3 assembly. It supplies no convergence, smoothness,
nonzero-functional, irreducibility, Laurent identity, rectangular kernel,
coefficient-model, continuation or final local-factor assertion.
