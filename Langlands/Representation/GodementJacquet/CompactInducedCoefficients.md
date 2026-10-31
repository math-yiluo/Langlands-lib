# Compact integral formula for normalized induced coefficients

This derived module retains the explicit integral characterization of the
published compact-picture duality. It concerns every admissible representation
of an actual block Levi over a p-adic field with supplied topological data, in
positive ambient rank. Field and coefficient-carrier universes are independent.

`compactInducedCoefficientKernel` pairs the value at `k` of an induced
smooth-dual section with the value at `k * g` of the original induced section.
The pairing is complex bilinear, without complex conjugation.

`exists_compactInducedCoefficientFormula` selects the compact open Iwasawa
subgroup and Haar probability measure from the proved
`glParabolicCompactScalarIntegral`. The subgroup and measure work for every
admissible inducing representation on the chosen carrier. The proof applies
`Induction.exists_integralDualEquiv`, using the continuous Levi projection,
the open kernel and square identity of the positive half modulus,
compact-open cofinality in the Levi, and the published preservation of
admissibility by normalized induction. Applying its pairing identity to the
right translate of the section gives the matrix coefficient formula.
Local constancy of the two-section pairing gives continuity on the compact
subgroup and hence integrability.

This is an internal specialization of published results. It supplies an actual
coefficient identity, with an unconditional choice of the subgroup, measure,
and equivalence under admissibility. It does not assert a finite expansion of
matrix zeta integrals, their convergence on the noncompact ambient group,
rational continuation, or reverse generation of the Laurent value module.
