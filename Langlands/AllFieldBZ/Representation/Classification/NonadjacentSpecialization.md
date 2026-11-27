# All-field port of `Langlands.Representation.Classification.NonadjacentSpecialization`

Lean module: `Langlands.AllFieldBZ.Representation.Classification.NonadjacentSpecialization`. Original module: `Langlands.Representation.Classification.NonadjacentSpecialization`; its mathematical content is
described in the Library file `Langlands/Representation/Classification/NonadjacentSpecialization.md`.

## Content

A nonzero invariant form between a supercuspidal `A` and `ν B~` forces `B ≅ ν A` (`twist_class_eq_of_length_ne_zero'`, and its rank-cast form `twist_class_eq_of_length_ne_zero`); no positive-rank supercuspidal class is fixed by `ν` (`sigma_ne_twist`).

The field is `F : Langlands.AllFieldBZ.LocalFieldPackage` (a field with no base field and no
characteristic hypothesis) and its local-field structure is `T : F.TopologicalData`, an
abbreviation of the Library structure `Langlands.LocalFieldData F.Carrier`. The module imports
the original module and uses its field-independent declarations directly. Each ported statement
is the original statement with the replacements listed under "Systematic changes", and each
proof is the original proof with the same replacements, except where listed below.

## Ported declarations

| Original declaration | All-field declaration |
| --- | --- |
| `Langlands.Classification.NonadjacentAssembly.twist_class_eq_of_length_ne_zero'` | `Langlands.AllFieldBZ.Classification.NonadjacentAssembly.twist_class_eq_of_length_ne_zero'` |
| `Langlands.Classification.NonadjacentAssembly.twist_class_eq_of_length_ne_zero` | `Langlands.AllFieldBZ.Classification.NonadjacentAssembly.twist_class_eq_of_length_ne_zero` |
| `Langlands.Classification.NonadjacentAssembly.sigma_ne_twist` | `Langlands.AllFieldBZ.Classification.NonadjacentAssembly.sigma_ne_twist` |

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

The field-independent declarations `Langlands.Classification.NonadjacentAssembly.leftKernel`, `left_nondegenerate` and `nonempty_equiv_of_forms_ne_zero` are used unchanged. In `sigma_ne_twist` the original appeals to integral twist freeness of cuspidal data; the port uses the all-field theorem `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductTwistOne.twist_one_ne_self` (`ρ.twist 1 ≠ ρ` for every cuspidal datum `ρ`), which is the case `n = 1` of that statement.

## Use

This module is part of the all-field proof of Zelevinsky 1980, Proposition 1.11(b)
(reducibility of adjacent supercuspidal products), whose final theorem is
`Langlands.AllFieldBZ.Classification.adjacentSupercuspidalProductReducibility` in
`Langlands.AllFieldBZ.Representation.Classification.AdjacentSupercuspidalProductReducibilityProof`.
