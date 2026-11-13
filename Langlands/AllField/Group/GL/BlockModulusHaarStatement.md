# All-field port of `Langlands.Group.GL.BlockModulusHaarStatement`

`Langlands.AllField.Group.GL.BlockModulusHaarStatement` is the all-field port of the Library module `Langlands.Group.GL.BlockModulusHaarStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Group.GL.BlockModulusHaarStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The explicit block modulus is the Haar module of Levi conjugation**

Bernstein--Zelevinsky define `mod_U(m)` by the scaling of a Haar measure of the
unipotent radical `U` under `u ↦ m u m⁻¹`. This proposition states that the
published explicit block modulus `T.leviModulus B` is that module, for every
Borel Haar measure on the actual block unipotent radical. It is a proposition
definition, not a proof.

## Imports from the port

- `Langlands.AllField.Group.GL.BlockModulus`

## Declarations

- `Langlands.AllField.GLBlockModulusHaarStatement` (def): For every local-field realization, ordered block shape `B`, Borel Haar measure
  `μ` on the actual block unipotent radical `U` and Levi element `m`, the image of `μ`
  under conjugation `u ↦ m u m⁻¹` is `δ_P(m)⁻¹ μ`, where `δ_P = T.leviModulus B` is the
  explicit block modulus.
