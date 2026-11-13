# All-field port of `Langlands.Representation.Derivative.MirabolicCharacter`

`Langlands.AllField.Representation.Derivative.MirabolicCharacter` is the all-field port of the Library module `Langlands.Representation.Derivative.MirabolicCharacter`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Derivative.MirabolicCharacter` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The positive Bernstein–Zelevinsky character on the actual mirabolic radical**

## Imports from the port

- `Langlands.AllField.Group.GL.Padic`

## Declarations

- `Langlands.LocalFieldData.mirabolicTheta` (def): The BZ character for every supplied local-field topology.

Public declarations of the original that are not re-declared here: `Langlands.Derivative.Mirabolic.lastCoordinate`, `Langlands.Derivative.Mirabolic.lastCoordinate_apply`, `Langlands.Derivative.Mirabolic.theta`, `Langlands.Derivative.Mirabolic.theta_apply`, `Langlands.Derivative.Mirabolic.theta_radicalElement`, `Langlands.Derivative.Mirabolic.norm_theta`, `Langlands.Derivative.Mirabolic.mulVec_last`, `Langlands.Derivative.Mirabolic.theta_isInvariant`, `Langlands.Derivative.Mirabolic.superdiagonalSum_radical`, `Langlands.Derivative.Mirabolic.theta_eq_standardCharacter_comp`, `Langlands.Derivative.Mirabolic.thetaContinuous`, `Langlands.Derivative.Mirabolic.theta_isOpen_ker`, `Langlands.PadicField.TopologicalData.mirabolicThetaContinuous`, `Langlands.PadicField.TopologicalData.mirabolicTheta_isOpen_ker`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
