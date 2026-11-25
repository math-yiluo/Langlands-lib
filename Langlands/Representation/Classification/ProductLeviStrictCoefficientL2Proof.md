# Square-integrable coefficients from strict fundamental Jacquet bounds

This exact interface applies the
published `ProductLeviSquareIntegrable.memLp_two_of_strictFundHypothesis`.
Its summation argument adapts the published strict-Lp proof
`ProductLeviSquareIntegrable.memLp_of_strict` in `ProductLeviSquareIntegrableLpProof`.

`Langlands.glProductLeviStrictCoefficientL2` proves
`GLProductLeviStrictCoefficientL2Statement.{uF,uV}` from
[`ProductLeviStrictCoefficientL2Statement`](ProductLeviStrictCoefficientL2Statement.md).
The proof introduces the statement's binders, installs the supplied field and
Levi topologies, and applies the published helper with exactly those inputs.
It adds no summation proof or auxiliary assumptions.

The field and carrier universes stay independent. The statement retains any
admissible actual Levi representation satisfying `StrictFundHypothesis`,
the supplied Cartan count, every supplied unitary central-character datum,
smooth-dual functional and vector, and every Borel Haar measure on the
quotient by the full centre. There is no irreducibility, nontriviality,
positive-rank, finite-length or global finite-spectrum premise.

The invoked helper in
[`ProductLeviSquareIntegrableSufficiencyProof`](ProductLeviSquareIntegrableSufficiencyProof.md)
bounds each coefficient by `cb * ∏ j, delta(lam j)^(1/2 + ε)` for a
coefficient-specific `ε > 0`. Squaring and multiplying by the inverse-modulus
cell-volume bound gives geometric ratios `fundWeight^(2*ε) < 1`. The finite
lattice sum and actual quotient-cell cover prove `MemLp` at exponent two for
the supplied Haar measure. These are the inputs and conclusion of the
published helper being applied; its proof is not repeated here.

This is an internal adapter to a published Library theorem. It neither
constructs the central character nor derives the strict fundamental
hypothesis; those remain premises of this interface. The whole strict GL
criterion remains a separate obligation. The target and all its imported
Lean/Markdown pairs are unchanged.

The dependency audit at Library base
`61f87bbe6fe6e5ffe1387e9640956e5d8d8c9fc5` covers 378 project modules in the
combined closure of this proof and the other generic helper. Every imported
Lean/Markdown pair matches the Library at that base, and no pair is missing.
The imports added for this proof are the published
`ProductLeviSquareIntegrableSufficiencyStatement` and
`ProductLeviSquareIntegrableSufficiencyProof`. Their source and proof were checked
for this reuse. No `WeakCritical` module is imported.

The four forbidden-name matches in the combined closure are unproved
proposition definitions and aggregate references in
`TemperedInductionStatement` and `TemperedSupportStatement`. No proof of their
unitarity or support conclusions is used. There is no dependency on segment
analytic classification, special-head exhaustion or existence, quotient
coverage, tempered block uniqueness, square-integrable classification or
exhaustion, regular exhaustion, weakly-critical support/refinement/minimality,
tempered exhaustion/unitarity/genericity, equal-exponent grouping, or the
forbidden proofs and transitive dependencies of these conclusions.
This preserves both
the strict GL criterion's independence and the product-Levi consumer's
independence. The named target and every pair it imports are unchanged.
