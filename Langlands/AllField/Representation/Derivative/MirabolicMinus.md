# All-field port of `Langlands.Representation.Derivative.MirabolicMinus`

`Langlands.AllField.Representation.Derivative.MirabolicMinus` is the all-field port of the Library module `Langlands.Representation.Derivative.MirabolicMinus`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Derivative.MirabolicMinus` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Mirabolic minus localization functors**

The unnormalized Bernstein–Zelevinsky functors `Ψ⁻ : P_(n+1) → GL_n` and
`Φ⁻ : P_(n+2) → P_(n+1)` act on the actual character-localized quotients by the
actual radicals. Their determinant-normalized versions twist the descended action by
the inverse half power of the residue-normalized determinant character. No Haar
automorphism modulus is identified with that character here.

## Imports from the port

- `Langlands.AllField.Group.GL.NormalizedCharacter`
- `Langlands.AllField.Representation.Derivative.MirabolicCharacter`

## Declarations

- `Langlands.AllField.Derivative.Mirabolic.phiMinusUnnormalized` (def): Unnormalized `Φ⁻`: localize at `θ_ψ` on `V_(n+2)`, then restrict the descended
  successor action along `P_(n+1) ≃ₜ* successorSubgroup n`.
- `Langlands.AllField.Derivative.Mirabolic.phiMinusQuotient` (abbrev): The canonical quotient map onto the actual `Φ⁻` carrier.
- `Langlands.AllField.Derivative.Mirabolic.phiMinusQuotient_surjective` (theorem).
- `Langlands.AllField.Derivative.Mirabolic.phiMinusQuotient_radical` (theorem): Radical elements act on `Φ⁻` quotient classes through `θ_ψ`.
- `Langlands.AllField.Derivative.Mirabolic.phiMinusUnnormalized_action` (theorem): `h • q(v) = q(successor h • v)` for unnormalized `Φ⁻`.

Public declarations of the original that are not re-declared here: `Langlands.Derivative.Mirabolic.continuousPullbackMap`, `Langlands.Derivative.Mirabolic.continuousPullback`, `Langlands.Derivative.Mirabolic.continuousPullbackFunctor`, `Langlands.Derivative.Mirabolic.psiMinusUnnormalized`, `Langlands.Derivative.Mirabolic.psiMinusQuotient`, `Langlands.Derivative.Mirabolic.psiMinusUnnormalized_obj_carrier`, `Langlands.Derivative.Mirabolic.psiMinusUnnormalized_obj_representation`, `Langlands.Derivative.Mirabolic.psiMinusQuotient_surjective`, `Langlands.Derivative.Mirabolic.ker_psiMinusQuotient`, `Langlands.Derivative.Mirabolic.psiMinusQuotient_radical`, `Langlands.Derivative.Mirabolic.psiMinusUnnormalized_action`, `Langlands.Derivative.Mirabolic.psiMinusUnnormalized_isSmooth`, `Langlands.Derivative.Mirabolic.psiMinusUnnormalized_map_quotient`, `Langlands.Derivative.Mirabolic.psiMinusUnnormalized_map_equivariant`, `Langlands.Derivative.Mirabolic.psiMinusUnnormalized_map_id`, `Langlands.Derivative.Mirabolic.psiMinusUnnormalized_map_comp`, `Langlands.Derivative.Mirabolic.phiMinusUnnormalized_obj_carrier`, `Langlands.Derivative.Mirabolic.phiMinusUnnormalized_obj_representation`, `Langlands.Derivative.Mirabolic.ker_phiMinusQuotient`, `Langlands.Derivative.Mirabolic.phiMinusUnnormalized_isSmooth`, `Langlands.Derivative.Mirabolic.phiMinusUnnormalized_map_quotient`, `Langlands.Derivative.Mirabolic.phiMinusUnnormalized_map_equivariant`, `Langlands.Derivative.Mirabolic.phiMinusUnnormalized_map_id`, `Langlands.Derivative.Mirabolic.phiMinusUnnormalized_map_comp`, `Langlands.Derivative.Mirabolic.psiMinusCharacter`, `Langlands.Derivative.Mirabolic.phiMinusCharacter`, `Langlands.Derivative.Mirabolic.isOpen_ker_psiMinusCharacter`, `Langlands.Derivative.Mirabolic.isOpen_ker_phiMinusCharacter`, `Langlands.Derivative.Mirabolic.psiMinus`, `Langlands.Derivative.Mirabolic.phiMinus`, `Langlands.Derivative.Mirabolic.psiMinus_eq`, `Langlands.Derivative.Mirabolic.phiMinus_eq`, `Langlands.Derivative.Mirabolic.psiMinus_obj_carrier`, `Langlands.Derivative.Mirabolic.psiMinus_action`, `Langlands.Derivative.Mirabolic.psiMinus_action_eq_smul`, `Langlands.Derivative.Mirabolic.psiMinus_map_quotient`, `Langlands.Derivative.Mirabolic.psiMinus_isSmooth`, `Langlands.Derivative.Mirabolic.psiMinus_map_equivariant`, `Langlands.Derivative.Mirabolic.psiMinus_map_id`, `Langlands.Derivative.Mirabolic.psiMinus_map_comp`, `Langlands.Derivative.Mirabolic.phiMinus_obj_carrier`, `Langlands.Derivative.Mirabolic.phiMinus_action`, `Langlands.Derivative.Mirabolic.phiMinus_action_eq_smul`, `Langlands.Derivative.Mirabolic.phiMinus_map_quotient`, `Langlands.Derivative.Mirabolic.phiMinus_isSmooth`, `Langlands.Derivative.Mirabolic.phiMinus_map_equivariant`, `Langlands.Derivative.Mirabolic.phiMinus_map_id`, `Langlands.Derivative.Mirabolic.phiMinus_map_comp`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
