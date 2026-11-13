# All-field port of `Langlands.Representation.RankinSelberg.AnalyticStatement`

`Langlands.AllField.Representation.RankinSelberg.AnalyticStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.AnalyticStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.AnalyticStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**JPSS convergence and rationality on actual coefficient models**

These are proposition definitions, not proofs of the JPSS analytic theorem.
The quotient measure is any measure satisfying the published compatibility
predicate `QuotientIntegration.IsCompatible`; its existence is a separate
proposition. The scope is admissible finite-type Whittaker type, including
reducible representations.

## Imports from the port

- `Langlands.AllField.Group.GL.Padic`

## Declarations

- `Langlands.AllField.RankinSelberg.normalizedAbsoluteValue` (def): Package the already proved residue-cardinality absolute value. No
  base-extending spectral norm is substituted for this normalization.
- `Langlands.AllField.RankinSelberg.normalizedAbsoluteValue_apply` (theorem).
- `Langlands.AllField.RankinSelberg.UnequalRankAnalyticStatement` (def): JPSS Theorem 2.7(i)-(ii) for all positive unequal ranks and all rectangular
  blocks. The rectangular measure is the actual product of the given additive
  Haar measure. No self-dual normalization is needed until the functional equation.
- `Langlands.AllField.RankinSelberg.UnequalRankCommonGeneratorStatement` (def): The same normalized reciprocal polynomial generates every allowed block
  family at fixed positive ranks, as asserted in JPSS Theorem 2.7(ii).

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.spectralPoint_eq_spectralParameter`, `Langlands.RankinSelberg.IsOfWhittakerType`, `Langlands.RankinSelberg.equalRankRationalValues`, `Langlands.RankinSelberg.EqualRankAnalyticConclusion`, `Langlands.RankinSelberg.unequalRankRationalValues`, `Langlands.RankinSelberg.UnequalRankAnalyticConclusion`, `Langlands.RankinSelberg.unequalRankValuesAt`, `Langlands.RankinSelberg.QuotientHaarExistenceStatement`, `Langlands.RankinSelberg.EqualRankAnalyticStatement`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
