# Residue-field comparison (M243.018)

`decompositionFieldResidueEquiv` is a ring equivalence from the actual
residue field of the valuation ring on the decomposition field to
`decompositionResidueField K A`, the quotient of the fixed subring by the
contracted maximal ideal. It lives in
`Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`.
Its parameters are `(K : Type u) {L : Type v} [Field K] [Field L]
[Algebra K L] [IsGalois K L] (A : ValuationSubring L)` and the isomorphism
is a Type-valued datum, not a proposition.

Source: Naganori Yamaguchi, NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean`,
lines 217–226 (declaration 219). The unchanged body first applies Mathlib's
`IsLocalRing.ResidueField.mapEquiv` to M243.006, then changes the quotient
ideal along the equality M243.017 using `Ideal.quotientEquivAlgOfEq ℤ`.
The fixed-subring ring equivalence and maximal-ideal equality are reused
by Lean name. No finiteness hypothesis is added; both residue fields
remain in `Type v`.

Modifications: namespace prefix `Langlands.NYLL`, narrowed imports, module
extraction and documentation, and the header's modification note. The
source `def`, complete body, docstring, universes and section variables
are retained. The sole import is the published M243.017 `MaximalIdealProof` module.
It supplies `decompositionFixedMaximalIdeal_eq_maximalIdeal`; its imports
also supply the M243.006 ring equivalence and the existing global instance
`FixedPoints.isLocalRing_subring`. No new locality instance is declared.

Registered source: `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The original copyright/author header is preserved and the existing
Apache-2.0 files `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are reused.
