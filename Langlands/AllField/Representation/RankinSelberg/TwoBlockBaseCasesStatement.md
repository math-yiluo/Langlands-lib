# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockBaseCasesStatement`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockBaseCasesStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockBaseCasesStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockBaseCasesStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Three two-block analytic base cases for the factors of pairs**

The three bases enumerated in JPSS 1983, §7.1, printed pages 438–439,
for both parts of Theorem (3.1), printed pages 404–405. Each target is the
published full multiplicativity statement with two blocks and one additional
arithmetic restriction. The actual ranks are `r + 1`, `t + 1`, `m i + 1`.
The source lower block order reverses in the actual upper induction, so the
adjacent-rank target has `m 0 = 0`. The analytic proofs and the normalized
lower-to-upper equivalence and factor transports are not supplied here.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.MultiplicativityStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockGammaDominantRankStatement` (def): The dominant-rank base of JPSS §7.1(1), proved in source Section 4:
  the test rank `r + 1` is at least the induced rank `t + 1`.
  This target asserts certified gamma multiplicativity.
- `Langlands.AllField.RankinSelberg.TwoBlockLDominantRankStatement` (def): The dominant-rank base of JPSS §7.1(1), proved in source Section 4:
  the test rank `r + 1` is at least the induced rank `t + 1`.
  This target asserts certified L-polynomial divisibility.
- `Langlands.AllField.RankinSelberg.TwoBlockGammaAdjacentRankStatement` (def): The adjacent-rank base of JPSS §7.1(2), treated in source Section 6.
  The rank-one block is first in the actual upper induction. With the rank sum,
  `t = r + 1` and `m 0 = 0` imply `m 1 = r`.
  This target asserts certified gamma multiplicativity.
- `Langlands.AllField.RankinSelberg.TwoBlockLAdjacentRankStatement` (def): The adjacent-rank base of JPSS §7.1(2), treated in source Section 6.
  The rank-one block is first in the actual upper induction. With the rank sum,
  `t = r + 1` and `m 0 = 0` imply `m 1 = r`.
  This target asserts certified L-polynomial divisibility.
- `Langlands.AllField.RankinSelberg.TwoBlockGammaRankOneStatement` (def): The rank-one test base of JPSS §7.1(3), treated in source §5.1–§5.4:
  the actual test rank is `r + 1 = 1`.
  This target asserts certified gamma multiplicativity.
- `Langlands.AllField.RankinSelberg.TwoBlockLRankOneStatement` (def): The rank-one test base of JPSS §7.1(3), treated in source §5.1–§5.4:
  the actual test rank is `r + 1 = 1`.
  This target asserts certified L-polynomial divisibility.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockBaseCasesStatement`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
