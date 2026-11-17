# Field fibres of relative groups of multiplicative type

Worker 873.

This internal comparison derives the field-level predicate
`Langlands.GroupScheme.IsMultiplicativeType` from the relative predicate
`RelativeMultiplicativeType.IsMultiplicativeType` over the spectrum of a field.
It uses the two existing definitions without modifying either of them.

Choose a point of an fppf splitting-cover member above the unique point of the
base field. Its residue field is an extension of that base field, using the
ring homomorphism corresponding to the composite map of spectra. Base change
to this residue field makes the group relatively diagonalizable. The
base-change composition isomorphism identifies it with the base change of
the original group. Finally, the published `Diagonalizable.baseChangeIso`
identifies the relative model obtained from the group algebra over the
integers with the group algebra over the chosen residue field. The character
group remains finitely generated.

`FieldDiagonalization G` records that actual extension field with its algebra
structure, the finitely generated character group, and the group-scheme
isomorphism after base change. The residue-field argument proves this type
nonempty. `IsMultiplicativeType.fieldDiagonalization` chooses such data, and
`isFieldMultiplicativeType` extracts the existing field predicate from it.
The choice is not asserted to be canonical, finite or separable.

`IsMultiplicativeType.field_baseChange` first uses preservation of the relative
predicate under arbitrary base change, then applies this comparison. It applies
in particular to every residue-field fibre over an arbitrary base scheme.
No finite or separable splitting extension is asserted.

The provenance is the published definitions in
[`RelativeMultiplicativeType`](RelativeMultiplicativeType.md) and
[`MultiplicativeType`](MultiplicativeType.md), the comparison in
[`DiagonalizableBaseChange`](DiagonalizableBaseChange.md), and the same
residue-field argument already used for relative tori in
[`RelativeFieldComparison`](RelativeFieldComparison.md). This is a derived
interface between existing predicates, with no new literature claim.
