# Proof of the conditional two-block analytic induction

Module `Langlands.Representation.GodementJacquet.TwoBlockMatrixAnalyticInductionProof`.
Authors: Worker 704 and Worker 1112.

## Result

`Langlands.GodementJacquet.twoBlockMatrixAnalyticInduction` proves exactly the
published proposition
`Langlands.GodementJacquet.TwoBlockMatrixAnalyticInductionStatement.{uF,uV}`
(module `Langlands.Representation.GodementJacquet.TwoBlockMatrixAnalyticInductionStatement`),
with its whole telescope unchanged. For every prime `p`, canonical p-adic field
`F`, positive two-block shape `m` with `∑ i, (m i + 1) = t + 1`, family of
smooth admissible block representations `σ i` (possibly reducible) with scalar
central quasicharacters, and block polynomials `Pi`, `PDual` and constants
satisfying the published normalized block data, the canonical normalized induced
representation `F.canonicalNormalizedProductInduced (succBlockShape m h) σ`
satisfies both `Padic.MatrixAnalyticAssertions` with `∏ i, Pi i` and
`Padic.IotaMatrixAnalyticAssertions` with `∏ i, PDual i`.

The intermediate theorem `twoBlockOrdinaryMatrixAnalyticInduction` proves the
ordinary statement `TwoBlockOrdinaryMatrixAnalyticInductionStatement` of
`TwoBlockAnalyticReduction`: block smoothness, admissibility and the ordinary
block assertions `Padic.MatrixAnalyticAssertions F (σ i) (P i)` imply the
ordinary assertion for the induced representation with `∏ i, P i`. Its central
character premise is not used.

## Proof

1. **Generator inputs** (`TwoBlock.twoBlock_matrixGeneratorInputs`, module
   `TwoBlockReverseRealization`). For the canonical residue cardinality,
   normalized absolute value and group Haar measures `generalLinearHaar`, all
   three components of `TwoBlockMatrixGeneratorInputs` hold:
   - common convergence and the forward inclusion come from
     `TwoBlock.twoBlock_forward_generatorInputs` (module
     `TwoBlockZetaExpansion`): the parabolic factorization of the Haar measure
     over a compact open subgroup `K` with `G = P K` (Godement–Jacquet 1972,
     printed 38), the compact integral formula for induced coefficients, and the
     finite product expansions of the coefficient and of the partial upper-block
     integral of the test (printed 40–41) write every induced zeta integral at
     `s + t/2` as a finite sum of products of block zeta integrals at
     `s + m₀/2` and `s + m₁/2`;
   - the reverse inclusion comes from `TwoBlock.twoBlock_reverse_generatorInput`:
     instead of the duality argument of Lemma 3.4.6 (printed 43–45), each product
     of two block rational values is realized directly, up to a nonzero
     constant, as the value of one induced coefficient, using a section supported
     on a single double coset `P K₀` and a test invariant on both sides under
     `K₀`.
2. **Ordinary assembly** (`matrixAnalyticAssertions_twoBlock_of_generators`,
   module `TwoBlockAnalyticAssembly`, with `1 < q` from
   `residueCardinality_gt_one`). The generator inputs and the block assertions
   give the convergence half-plane, rational continuation for every test and
   bi-smooth coefficient, and the normalized-generator equality with both
   inclusions.
3. **Transformed predicate** (`twoBlockMatrixAnalyticInduction_of_ordinary`,
   module `TwoBlockAnalyticReduction`). The ordinary statement applied to the
   original blocks gives the first conjunct. Applied to the reversed
   inverse-transpose block family (with the inverse central characters and the
   transported block assertions for `PDual`), it gives the transformed assertion
   through the published upper-to-reversed-upper normalized induction
   equivalence (`Padic.iotaMatrixAnalyticAssertions_succBlocks_iff`).

The proof itself only fixes the canonical Borel structures on `F` and on each
`GL_(n+1)(F)` (the instances used by the `Padic` predicates) and composes these
theorems.

## Scope

This module proves the analytic/product-generator half only. It assumes no
irreducibility, Whittaker type, finite length, factor existence, coefficient
expansion or induction equivalence; the block data are exactly the published
premises. The Fourier functional equation of the induced representation is a
separate task.
