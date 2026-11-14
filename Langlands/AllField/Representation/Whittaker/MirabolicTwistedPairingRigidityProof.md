# All-field port of `Langlands.Representation.Whittaker.MirabolicTwistedPairingRigidityProof`

`Langlands.AllField.Representation.Whittaker.MirabolicTwistedPairingRigidityProof` is the all-field port of the Library module `Langlands.Representation.Whittaker.MirabolicTwistedPairingRigidityProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Whittaker.MirabolicTwistedPairingRigidityProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**JPSS finite-spectral-exception mirabolic pairing rigidity**

The proof of `MirabolicTwistedPairingRigidityStatement` in every rank: the
induction of `MirabolicPairingRigidityStep` with its three inputs supplied by the
published proofs of the two unnormalized `Φ⁻` statements and of functional
multiplicity.

## Imports from the port

- `Langlands.AllField.Representation.Derivative.MirabolicMinusIrreducibleProof`
- `Langlands.AllField.Representation.Derivative.MirabolicMinusPairingTransferProof`
- `Langlands.AllField.Representation.RankinSelberg.EqualRankFrobeniusProof`
- `Langlands.AllField.Representation.RankinSelberg.ZeroRowLastRowCutoffProofSupplement`
- `Langlands.AllField.Representation.Whittaker.MirabolicFunctionalMultiplicityProof`
- `Langlands.AllField.Representation.Whittaker.MirabolicPairingRigidityStepSupplement`

## Declarations

- `Langlands.AllField.Whittaker.mirabolicTwistedPairingRigidity` (theorem): JPSS 1983, §1.5, Corollary 2: outside a finite set of spectral values
  `q ^ (-s)`, a nonzero twisted bilinear form on two irreducible smooth mirabolic
  representations forces both to be equivalent to the compact model.
