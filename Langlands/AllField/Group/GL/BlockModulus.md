# All-field port of `Langlands.Group.GL.BlockModulus`

`Langlands.AllField.Group.GL.BlockModulus` is the all-field port of the Library module `Langlands.Group.GL.BlockModulus`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

The original uses the canonical topological data `F.canonicalTopologicalData` of the p-adic field. The port uses the supplied data `T : LocalFieldData F` throughout. Where the original quantifies over a p-adic field with its canonical data, the port quantifies over a field `F` and arbitrary data `T`.

Source: the original module `Langlands.Group.GL.BlockModulus` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Explicit positive block modulus characters**

For the standard upper block parabolic the factor contributed by blocks `i < j`
is `|det m_i| ^ n_j / |det m_j| ^ n_i`. The character is built from these actual
determinants. Its interpretation as Haar scaling is a separate theorem.

## Imports from the port

- `Langlands.AllField.Group.GL.NormalizedCharacter`
- `Langlands.AllField.Group.GL.PadicBlocks`

## Declarations

- `Langlands.LocalFieldData.blockDeterminantNorm` (def): The actual normalized determinant of one diagonal block.
- `Langlands.LocalFieldData.blockDeterminantNorm_apply` (theorem).
- `Langlands.LocalFieldData.leviModulus` (def): The full positive standard upper-block modulus formula on the actual Levi.
- `Langlands.LocalFieldData.leviModulus_apply` (theorem).
- `Langlands.LocalFieldData.normOneLevi` (def): Simultaneous norm-one determinant conditions define an actual open subgroup.
- `Langlands.LocalFieldData.mem_normOneLevi` (theorem).
- `Langlands.LocalFieldData.normOneLevi_le_ker_leviModulus` (theorem).
- `Langlands.LocalFieldData.isOpen_normOneLevi` (theorem).
- `Langlands.LocalFieldData.isOpen_ker_leviModulus` (theorem).
- `Langlands.LocalFieldData.leviHalfModulus` (def): The positive complex half of the full modulus, used for induction.
- `Langlands.LocalFieldData.leviHalfModulus_apply` (theorem).
- `Langlands.LocalFieldData.leviHalfModulus_eq_one` (theorem).
- `Langlands.LocalFieldData.isOpen_ker_leviHalfModulus` (theorem).
- `Langlands.LocalFieldData.parabolicHalfModulus` (def): The positive half character on the parabolic, through its actual projection.
- `Langlands.LocalFieldData.parabolicHalfModulus_apply` (theorem).
- `Langlands.LocalFieldData.parabolicHalfModulus_section` (theorem).
- `Langlands.LocalFieldData.isOpen_ker_parabolicHalfModulus` (theorem).

Public declarations of the original that are not re-declared here: `Langlands.PadicField.TopologicalData.parabolicModulus`, `Langlands.PadicField.TopologicalData.parabolicModulus_apply`, `Langlands.PadicField.TopologicalData.parabolicModulus_section`, `Langlands.PadicField.TopologicalData.parabolicModulus_unipotent`, `Langlands.PadicField.TopologicalData.isOpen_ker_parabolicModulus`, `Langlands.PadicField.TopologicalData.continuous_leviModulus`, `Langlands.PadicField.TopologicalData.continuous_parabolicModulus`, `Langlands.PadicField.TopologicalData.leviModulus_scalar`, `Langlands.PadicField.TopologicalData.leviHalfModulus_sq`, `Langlands.PadicField.TopologicalData.parabolicHalfModulus_unipotent`, `Langlands.PadicField.TopologicalData.inverseHalf_leviModulus`, `Langlands.PadicField.TopologicalData.leviModulus_eq`, `Langlands.PadicField.TopologicalData.parabolicModulus_eq`, `Langlands.PadicField.TopologicalData.leviHalfModulus_eq`, `Langlands.PadicField.TopologicalData.parabolicHalfModulus_eq`, `Langlands.PadicField.canonicalLeviModulus`, `Langlands.PadicField.canonicalParabolicModulus`, `Langlands.PadicField.canonicalLeviHalfModulus`, `Langlands.PadicField.canonicalParabolicHalfModulus`, `Langlands.PadicField.isOpen_ker_canonicalLeviModulus`, `Langlands.PadicField.isOpen_ker_canonicalParabolicModulus`, `Langlands.PadicField.isOpen_ker_canonicalLeviHalfModulus`, `Langlands.PadicField.isOpen_ker_canonicalParabolicHalfModulus`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation (see also the next paragraph).

The original lemmas `leviModulus_eq`, `parabolicModulus_eq`, `leviHalfModulus_eq` and `parabolicHalfModulus_eq` compare the moduli computed from two realizations `T` and `U` of the same p-adic field. The port works with one supplied `T : LocalFieldData F` throughout and never changes the realization, so these lemmas are not ported.
