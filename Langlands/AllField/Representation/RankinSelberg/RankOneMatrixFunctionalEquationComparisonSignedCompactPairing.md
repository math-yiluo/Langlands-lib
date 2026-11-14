# All-field port of `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSignedCompactPairing`

`Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSignedCompactPairing` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSignedCompactPairing`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSignedCompactPairing` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Exact compact Whittaker pairing with the actual signed Fourier orbit.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonHaarShear`
- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSignedOrbitSmooth`
- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSupportedSynthesis`

## Declarations

- `Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis.weightedCompactMatrixLift` (def): A supported matrix lift of the inverse determinant twist of one actual
  compact induced function. The lift is chosen independently of the second test.
- `Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis.weightedCompactMatrixLift_support` (theorem).
- `Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis.weightedCompactMatrixLift_orbit` (theorem): The two inverse determinant powers cancel exactly in the true orbit integral.
- `Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis.integral_signedUnipotentDualKernel_eq_weightedOrbit` (theorem): The inner dual kernel is literally the weighted signed Fourier orbit,
  multiplied by the same second test. No convergence premise is used here.
- `Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis.integral_signedUnipotentShearedKernel_eq_compactPairing` (theorem): The sheared original kernel reconstructs the input compact function at
  its natural determinant weight, pointwise at every group element.
- `Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis.signedFourierOrbitOfCompact` (def): The literal natural-weight signed Fourier orbit of the fixed supported
  lift of a compact input. No compact-support claim is made for the output.
- `Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis.signedFourierOrbitOfCompact_left` (theorem).
- `Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis.signedFourierOrbitOfCompact_locallyConstant` (theorem).
- `Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis.continuous_signedFourierOrbitOfCompact` (theorem).
- `Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis.integrable_compact_signedWeyl_fourier_pairing` (theorem): Compact inputs admit the actual signed-Weyl Fourier pairing with every
  second Schwartz test. The proof uses genuine sheared product convergence.
- `Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis.compact_signedFourier_pairing` (theorem): The exact compact pairing identity: genuine convergence on both sides,
  the original compact input, and the actual signed Fourier orbit of its one
  fixed supported lift. The same supplied self-dual measure is used throughout.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.CompactWhittakerSynthesis.weightedCompactMatrixLift_orbit_integrable`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
