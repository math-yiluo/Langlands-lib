# All-field port of `Langlands.Representation.Classification.InverseTransposeHelpers`

Lean module: `Langlands.AllFieldBZ.Representation.Classification.InverseTransposeHelpers`. Original module: `Langlands.Representation.Classification.InverseTransposeHelpers`; its mathematical content is
described in the Library file `Langlands/Representation/Classification/InverseTransposeHelpers.md`.

## Content

Inverse-transpose constructions for normalized products: the pullback `hermitianItPullback` along `g ↦ ᵗg⁻¹`, Gelfand–Kazhdan in every positive rank (`hermitianGelfandKazhdanEquiv`: the pullback of an irreducible admissible representation is its smooth dual), the block reversal of a normalized product under inverse transpose (`hermitianItPullbackProductIso`) and products over equal shapes (`hermitianProductFunctor_obj_congr`).

The field is `F : Langlands.AllFieldBZ.LocalFieldPackage` (a field with no base field and no
characteristic hypothesis) and its local-field structure is `T : F.TopologicalData`, an
abbreviation of the Library structure `Langlands.LocalFieldData F.Carrier`. The module imports
the original module and uses its field-independent declarations directly. Each ported statement
is the original statement with the replacements listed under "Systematic changes", and each
proof is the original proof with the same replacements, except where listed below.

## Ported declarations

| Original declaration | All-field declaration |
| --- | --- |
| `Langlands.Classification.hermitianItPullback` | `Langlands.AllFieldBZ.Classification.hermitianItPullback` |
| `Langlands.Classification.hermitianGelfandKazhdanEquiv` | `Langlands.AllFieldBZ.Classification.hermitianGelfandKazhdanEquiv` |
| `Langlands.Classification.hermitianItPullbackProductIso` | `Langlands.AllFieldBZ.Classification.hermitianItPullbackProductIso` |
| `Langlands.Classification.hermitianProductFunctor_obj_congr` | `Langlands.AllFieldBZ.Classification.hermitianProductFunctor_obj_congr` |

## Systematic changes

- `Langlands.PadicField.{u} p` becomes `Langlands.AllFieldBZ.LocalFieldPackage.{u}`; the prime
  `p` and its `Fact p.Prime` instance are removed from binders and quantifiers, and the
  corresponding explicit arguments are dropped.
- Normalization API names on `T` (for example `Integers`, `ord`, `normalizedAbs`, `uniformizer`)
  resolve to `Langlands.LocalFieldData`.
- Every ported declaration `Langlands.X` is renamed `Langlands.AllFieldBZ.X` (with
  `PadicField.TopologicalData` replaced by `LocalFieldPackage.TopologicalData`). References to
  declarations that already have all-field versions in the Library use those versions (for
  example `Langlands.AllFieldBZ.Derivative.generalLinearDerivative` for
  `Langlands.Derivative.generalLinearDerivative`, and the `_allFieldBZ` versions of the
  `Langlands.GeneralLinear` declarations such as `compactOpen_cofinal`).
- References to field-independent declarations of the original module and of other p-adic
  modules are written with their full original names, so those declarations are used unchanged.
  Private field-independent helpers, which cannot be referenced from another module, are
  repeated as private declarations.

## Changes beyond the systematic replacements

Two proofs use different inputs. `hermitianGelfandKazhdanEquiv` applies the Gelfand–Kazhdan theorem for every nonarchimedean local field, `Langlands.LocalField.gelfandKazhdanContragredient` (Bernstein–Zelevinsky 1976, Theorem 7.3), instead of the p-adic theorem and its comparison with the canonical norm topology. `hermitianItPullbackProductIso` uses the all-field block reversal `Langlands.AllField.GodementJacquet.inverseTransposeProductReversalEquiv`; its positivity hypothesis on the rank is kept (as `_hn`) so that the statement is unchanged, although this proof does not use it.

## Use

This module is part of the all-field proof of Zelevinsky 1980, Proposition 1.11(b)
(reducibility of adjacent supercuspidal products), whose final theorem is
`Langlands.AllFieldBZ.Classification.adjacentSupercuspidalProductReducibility` in
`Langlands.AllFieldBZ.Representation.Classification.AdjacentSupercuspidalProductReducibilityProof`.
