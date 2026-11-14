# All-field supplement to `Langlands.AllField.Representation.RankinSelberg.EqualRankContinuedFormsProof`

`Langlands.AllField.Representation.RankinSelberg.EqualRankContinuedFormsProofSupplement` supplements the Library module `Langlands.AllField.Representation.RankinSelberg.EqualRankContinuedFormsProof`, the existing all-field port of `Langlands.Representation.RankinSelberg.EqualRankContinuedFormsProof`. The original belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The module imports the original, so the field-independent declarations of the original are available to it unchanged. This module re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use and that `Langlands.AllField.Representation.RankinSelberg.EqualRankContinuedFormsProof` does not already provide. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Source: the original module `Langlands.Representation.RankinSelberg.EqualRankContinuedFormsProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Construction of the continued normalized equal-rank trilinear forms**

The cleared rational continuations of the original and Fourier-dual equal-rank
integrals have unique Laurent lifts, linear in the test triple. Evaluating them at
the nonzero spectral points `q^(-s)` and `q^(-(1-s))` gives trilinear forms for
every complex parameter. Their twisted invariance follows from the monomial
translation laws of the lifts, and they agree with the normalized rational
continuations wherever the relevant continuation is regular.

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.PadicRowFourierEquivarianceProof`
- `Langlands.AllField.Representation.RankinSelberg.EqualRankCharacterChange`
- `Langlands.AllField.Representation.RankinSelberg.EqualRankContinuedFormsProof`
- `Langlands.AllField.Representation.RankinSelberg.EqualRankContinuedFormsStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.padic_rowFourier_equivariance` (theorem): The p-adic row Fourier equivariance, read in the instance context of the
  continued-forms statement with the normalized absolute value.
- `Langlands.AllField.RankinSelberg.padic_row_translate_exists` (theorem): Right translates of row Schwartz--Bruhat functions exist, in the instance
  context of the continued-forms statement (first half of the published
  equivariance theorem).
- `Langlands.AllField.RankinSelberg.equalRankContinuedForms` (theorem): **Continued normalized equal-rank trilinear forms.** Proof of
  `EqualRankContinuedFormsStatement`.

Declarations of the original re-declared by `Langlands.AllField.Representation.RankinSelberg.EqualRankContinuedFormsProof` and therefore not here: `Langlands.RankinSelberg.normalizedAbsoluteValue_det_eq_zpow`, `Langlands.RankinSelberg.padic_row_instances`.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.rowFourierMap`, `Langlands.RankinSelberg.isRowFourierPair_rowFourierMap`, `Langlands.RankinSelberg.eq_rowFourierMap`, `Langlands.RankinSelberg.rowFourierMap_translate`, `Langlands.RankinSelberg.det_inverseTranspose`, `Langlands.RankinSelberg.abv_det_inverseTranspose`, `Langlands.RankinSelberg.dual_spectral_factor`, `Langlands.RankinSelberg.laurentEval_spectralUnit_T_mul`, `Langlands.RankinSelberg.laurentEval_spectralUnit_dual_factor`, `Langlands.RankinSelberg.laurentLift_translate_original`, `Langlands.RankinSelberg.laurentLift_translate_dual`, `Langlands.RankinSelberg.continuedForms_of_laws`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
