# All-field supplement to `Langlands.AllField.Representation.Whittaker.MirabolicCompactTwistedPairingProof`

`Langlands.AllField.Representation.Whittaker.MirabolicCompactTwistedPairingProofSupplement` supplements the Library module `Langlands.AllField.Representation.Whittaker.MirabolicCompactTwistedPairingProof`, the existing all-field port of `Langlands.Representation.Whittaker.MirabolicCompactTwistedPairingProof`. The original belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The module imports the original, so the field-independent declarations of the original are available to it unchanged. This module re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use and that `Langlands.AllField.Representation.Whittaker.MirabolicCompactTwistedPairingProof` does not already provide. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Whittaker.MirabolicCompactTwistedPairingProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The compact mirabolic twisted pairing is one-dimensional**

For a p-adic field, every unitary additive character `ψ`, every rank `n` and
every `s : ℂ`, the space of bilinear forms `B` on the actual compact mirabolic
model with `B (τ g f₁) (τ g f₂) = |det g|^(-s) B f₁ f₂` is linearly equivalent to `ℂ`.

## Imports from the port

- `Langlands.AllField.Group.GL.CompactOpenSupplement`
- `Langlands.AllField.Representation.RankinSelberg.LastRowCompactOrbitProof`
- `Langlands.AllField.Representation.Shahidi.Induction`
- `Langlands.AllField.Representation.Whittaker.MirabolicCompactTwistedPairingProof`
- `Langlands.AllField.Representation.Whittaker.MirabolicPairingStatementSupplement`

## Declarations

- `Langlands.AllField.Whittaker.mirabolicCompactTwistedPairing` (theorem): The actual compact mirabolic twisted pairing is one-dimensional.

Declarations of the original re-declared by `Langlands.AllField.Representation.Whittaker.MirabolicCompactTwistedPairingProof` and therefore not here: `Langlands.Whittaker.MirabolicCompactTwistedPairing.isOpenNormOne_normalizedAbsoluteValue`.

Public declarations of the original that are not re-declared here: `Langlands.Whittaker.MirabolicCompactTwistedPairing.nonempty_linearEquiv_complex`, `Langlands.Whittaker.MirabolicCompactTwistedPairing.isSmooth_characterRepresentation`, `Langlands.Whittaker.MirabolicCompactTwistedPairing.mirabolicCharacter_scale_neg_one_mul`, `Langlands.Whittaker.MirabolicCompactTwistedPairing.nonempty_oppositeForms_equiv`, `Langlands.Whittaker.MirabolicCompactTwistedPairing.valuative_nonarchimedean`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
