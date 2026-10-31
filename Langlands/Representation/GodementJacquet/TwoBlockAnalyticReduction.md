# Reduction of two-block matrix analytics to ordinary induction

This internal statement and proved reduction isolate the remaining ordinary
analytic-induction theorem. The module does not prove that theorem or the closed
parent statement without its explicit ordinary-induction hypothesis.

`TwoBlockOrdinaryMatrixAnalyticInductionStatement` quantifies every prime,
canonical p-adic field, two positive block ranks with the prescribed total,
dependent family of complex modules and actual block representations. The field
and carrier universes remain independent. It assumes specified scalar central
quasicharacters acting on the whole carriers, smoothness, admissibility, and the
ordinary matrix analytic assertion for each block with a proposed polynomial.
Its conclusion is the ordinary matrix analytic assertion for the actual
canonical normalized upper induction with the product polynomial. Reducible
blocks are allowed. The statement has no Fourier-data, additive-character or
self-dual-measure hypothesis.

`twoBlockMatrixAnalyticInduction_of_ordinary` proves the entire published
`TwoBlockMatrixAnalyticInductionStatement` from this ordinary statement. For the
first conjunct it projects the ordinary block analytic assertions from the
supplied functional-equation packages and applies ordinary induction directly.

For the transformed conjunct the proof uses the actual family
`reversedInverseTransposeBlocks m σ`. Its carriers, ranks and module structures
are the original dependent family in reversed order. Admissibility passes along
the inverse-transpose continuous group equivalence, and supplies smoothness.
The scalar central quasicharacter of each pulled-back block is the inverse of
the corresponding original quasicharacter; this is proved from the scalar-matrix
formula in `TwoBlockAnalyticReversal`. The supplied transformed block analytic
assertions become ordinary assertions for these pullbacks, with polynomials
`i ↦ PDual i.rev`. Applying ordinary induction to this complete family gives
the ordinary analytic predicate of its actual normalized upper induction.
Finally, `Padic.iotaMatrixAnalyticAssertions_succBlocks_iff` transports that
predicate to the inverse-transpose coefficients of the original induced
representation. Its proof uses the actual upper-to-opposite-to-reversed-upper
induction equivalence before reindexing the polynomial product.

Every analytic assertion retains its common convergence bound before all tests
and coefficients, actual integrability, guarded rational continuation, and
equality of the entire Laurent module with its proposed normalized generator.
No contragredient identification or irreducibility hypothesis is used. The
published parent telescope, including the supplied self-dual additive measure,
is unchanged. This reduction uses only the two analytic projections of each
block package, so its Fourier witnesses and self-duality premise need no
additional transformation.

The provenance is internal: the existing closed parent statement, its analytic
predicates, and the proved actual family, scalar-action, admissibility and
coefficient transports in `TwoBlockAnalyticReversal`. The noncompact ordinary
convergence and product-integral calculations, and both Laurent-span inclusions
for ordinary induction, are still required to prove the new ordinary statement.
