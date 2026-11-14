# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockLowerIntegrandRegularity`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerIntegrandRegularity` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockLowerIntegrandRegularity`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockLowerIntegrandRegularity` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Local constancy and measurability of the actual Section 4.7 lower integrand.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerUnfoldingIntegrandData`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.partialSection_locallyConstant` (theorem): Local constancy of the complete row-translate family passes through the fixed
  first-block Fourier integral, for the supplied additive Haar measure.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.sectionEval_locallyConstant` (theorem): Evaluation of an actual smooth opposite-parabolic section is locally constant.
  The tensor carrier needs no topology.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.scalarSection_locallyConstant` (theorem): Every fixed block contraction of a smooth section is locally constant in the
  ambient group coordinate. In particular, this applies at the Levi identity.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.coefficient_locallyConstant` (theorem): Actual coefficient-image functions of a smooth representation are locally
  constant as scalar functions on the group.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.groupIntegrand_locallyConstant` (theorem): The actual group integrand is locally constant. Smoothness of the test
  representation is sufficient; no growth or convergence premise is used.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.integrand_locallyConstant` (theorem): Local constancy descends to the actual lower quotient using its quotient
  topology and the proved representative-independent integrand.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.integrand_continuous` (theorem): The descended lower integrand is continuous.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.integrand_measurable` (theorem): Borel measurability of the exact Section 4.7 lower integrand for every
  supplied section, coefficient, row test and additive Fourier Haar measure.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockLowerUnfolding.continuousIntegrand`, `Langlands.RankinSelberg.TwoBlockLowerUnfolding.continuousIntegrand_apply`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
