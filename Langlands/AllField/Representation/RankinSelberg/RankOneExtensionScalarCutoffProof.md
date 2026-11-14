# All-field port of `Langlands.Representation.RankinSelberg.RankOneExtensionScalarCutoffProof`

`Langlands.AllField.Representation.RankinSelberg.RankOneExtensionScalarCutoffProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneExtensionScalarCutoffProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field, carrying either bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`) or the corresponding instances (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`. Declarations that take explicit data `T : F.TopologicalData` in the original take explicit data `T : LocalFieldData F` in the port.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneExtensionScalarCutoffProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Proof of the same-model scalar Fourier cutoff for the early JPSS Lemma (5.5)**

The cutoff set is a principal-unit neighborhood of `1`, small enough that the
quasicharacter is trivial on it, that it lies in the given open set, and that
the scalar diagonal matrices it defines fix a vector representing `f₂`.
The proof follows the paired Markdown.

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.PadicLatticeGeometryProof`
- `Langlands.AllField.Representation.RankinSelberg.RankOneExtensionScalarCutoffStatement`
- `Langlands.AllField.Representation.RankinSelberg.ZeroRowLastRowCutoffProofSupplement`

## Declarations

- `Langlands.AllField.RankinSelberg.ScalarCutoffProof.cutoffSet` (def): The cutoff set: elements of valuation one congruent to one modulo `π^n`.
  Its units are exactly the principal units of level `n`.
- `Langlands.AllField.RankinSelberg.ScalarCutoffProof.mem_cutoffSet_iff` (theorem).
- `Langlands.AllField.RankinSelberg.ScalarCutoffProof.cutoffSet_isOpen` (theorem).
- `Langlands.AllField.RankinSelberg.ScalarCutoffProof.cutoffSet_isCompact_isClosed` (theorem).
- `Langlands.AllField.RankinSelberg.ScalarCutoffProof.one_mem_cutoffSet` (theorem).
- `Langlands.AllField.RankinSelberg.ScalarCutoffProof.zero_not_mem_cutoffSet` (theorem).
- `Langlands.AllField.RankinSelberg.ScalarCutoffProof.exists_unit_of_mem_cutoffSet` (theorem).
- `Langlands.AllField.RankinSelberg.rankOneExtensionScalarCutoff` (theorem): The same-model scalar Fourier cutoff for the early JPSS Lemma (5.5).

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.ScalarCutoffProof.scalarBlockHom`, `Langlands.RankinSelberg.ScalarCutoffProof.scalarDiagonal`, `Langlands.RankinSelberg.ScalarCutoffProof.scalarDiagonal_one`, `Langlands.RankinSelberg.ScalarCutoffProof.lowerBlock_eq_mul`, `Langlands.RankinSelberg.ScalarCutoffProof.embeddedLowerBlock_eq_mul`, `Langlands.RankinSelberg.ScalarCutoffProof.scalar_ne_firstTrailing`, `Langlands.RankinSelberg.ScalarCutoffProof.embeddedLowerBlock_trailing_row`, `Langlands.RankinSelberg.ScalarCutoffProof.embeddedLowerBlock_scalar_column`, `Langlands.RankinSelberg.ScalarCutoffProof.embeddedLowerBlock_mul_smearing`, `Langlands.RankinSelberg.ScalarCutoffProof.smearing_mem_upperUnipotent`, `Langlands.RankinSelberg.ScalarCutoffProof.standardCharacter_smearing`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
