# All-field supplement to `Langlands.AllField.Representation.Whittaker.MirabolicPairingStatement`

`Langlands.AllField.Representation.Whittaker.MirabolicPairingStatementSupplement` supplements the Library module `Langlands.AllField.Representation.Whittaker.MirabolicPairingStatement`, the existing all-field port of `Langlands.Representation.Whittaker.MirabolicPairingStatement`. The original belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The module imports the original, so the field-independent declarations of the original are available to it unchanged. This module re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use and that `Langlands.AllField.Representation.Whittaker.MirabolicPairingStatement` does not already provide. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Whittaker.MirabolicPairingStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Irreducible mirabolic functionals and twisted pairings**

Proposition targets for the consequences of JPSS (1983), Proposition 1.4 and
Section 1.5, used in Section 2.10. No classification or proof is asserted here.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AnalyticStatementSupplement`
- `Langlands.AllField.Representation.Whittaker.MirabolicPairingStatement`

## Declarations

- `Langlands.AllField.Whittaker.MirabolicTwistedPairingRigidityStatement` (def): JPSS Section 1.5, Corollary 2: outside finitely many spectral values,
  a nonzero twisted bilinear form on two irreducible smooth mirabolic
  representations forces both to be equivalent to the actual compact model.
- `Langlands.AllField.Whittaker.MirabolicCompactTwistedPairingStatement` (def): The compact standard representation paired with itself has a nonzero,
  exactly one-dimensional twisted form space for every exponent, as used in
  JPSS Section 2.10, printed p.398.

Declarations of the original re-declared by `Langlands.AllField.Representation.Whittaker.MirabolicPairingStatement` and therefore not here: `Langlands.Whittaker.MirabolicFunctionalMultiplicityStatement`.

Public declarations of the original that are not re-declared here: `Langlands.Whittaker.MirabolicPairingStatement`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
