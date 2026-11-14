# All-field port of `Langlands.Representation.RankinSelberg.AdjacentRankJointShell`

`Langlands.AllField.Representation.RankinSelberg.AdjacentRankJointShell` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.AdjacentRankJointShell`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.AdjacentRankJointShell` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Compact joint determinant shells in JPSS Section 6.3, formulas (5) and (11).

## Imports from the port

- `Langlands.AllField.Group.GL.PadicBlocksSupplement`
- `Langlands.AllField.Representation.RankinSelberg.AdjacentRankDeterminantShells`
- `Langlands.AllField.Representation.RankinSelberg.AdjacentRankModelConvergenceProof`
- `Langlands.AllField.Representation.RankinSelberg.WhittakerRowSliceCompactSupportProof`

## Declarations

- `Langlands.AllField.RankinSelberg.Padic.exists_matrixTest_determinantOrder_lowerBound` (theorem): A square matrix test gives a lower bound for the determinant order wherever
  its restriction to the actual general linear group is nonzero.
- `Langlands.AllField.RankinSelberg.Padic.exists_whittakerRow_determinantOrder_lowerBound` (theorem): Smooth Whittaker row data likewise has determinant order bounded below.
  This is the pointwise support argument, before integration.
- `Langlands.AllField.RankinSelberg.Padic.adjacentRankJointShell` (def): The total determinant shell `ord(det g) + ord(det h) = m`.
- `Langlands.AllField.RankinSelberg.Padic.isClopen_adjacentRankJointShell` (theorem).
- `Langlands.AllField.RankinSelberg.Padic.adjacentRankJointShellKernel` (def): The actual sheared double integrand on a fixed total determinant shell.
  The scalar multiplier `a` accommodates all character and norm weights.
- `Langlands.AllField.RankinSelberg.Padic.adjacentRankJointShellKernel_mk` (theorem).
- `Langlands.AllField.RankinSelberg.Padic.continuous_adjacentRankJointShellKernel` (theorem).
- `Langlands.AllField.RankinSelberg.Padic.hasCompactSupport_adjacentRankJointShellKernel` (theorem): Each total determinant shell has compact joint support. Only smoothness of
  the first representation is needed; no growth hypothesis on the second function
  or scalar multiplier enters this support argument.
- `Langlands.AllField.RankinSelberg.Padic.integrable_adjacentRankJointShellKernel` (theorem): Absolute joint convergence of the fixed-shell double integral for any
  Borel measures finite on compact sets.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.adjacentRankShiftedPairing`, `Langlands.RankinSelberg.adjacentRankShiftedPairing_mk`, `Langlands.RankinSelberg.continuous_adjacentRankShiftedPairing`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
