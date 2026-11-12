# Finite separable stabilizer field of an actual almost-simple factor

This internal construction starts with an actual finite almost-simple product
presentation of the base change of a group scheme from a field `k` to a field `L`,
in an arbitrary universe. Its canonical factor action requires the base-changed
ambient group to be smooth and affine. The selected factor stabilizer consists
exactly of the `k`-automorphisms of `L` whose canonical action fixes that index.
The field `factorStabilizerField` is the actual intermediate field fixed by this
subgroup.

If the original group is almost-simple, the factor index type is nonempty.
Indeed, an empty product makes any two pulled-back test-scheme points equal by
the coordinate extensionality theorem. Faithful fpqc pullback along a field
extension reflects their commutation, contradicting the published
noncommutativity clause. This result needs no Galois, smoothness, or affineness
hypothesis beyond the actual product presentation and original almost-simplicity.

For the remaining results, `L/k` is Galois and the original group scheme is
quasi-compact, quasi-separated, and locally of finite presentation. The published
finite field of definition of the actual projection idempotent has pointwise
fixer contained in this stabilizer. Its fixer is open in the Krull topology,
so the stabilizer is open and therefore closed. Mathlib's infinite Galois
correspondence then identifies the fixer of `factorStabilizerField` with precisely
the factor stabilizer. The openness criterion proves that this field is finite
over `k`; separability follows because it is an intermediate field of a Galois
extension. In particular, an automorphism fixes this field pointwise if and only
if it fixes the selected actual factor index.

These are derived uses of the published finite endomorphism model and Mathlib's
infinite Galois correspondence. They do not require a finite-degree Galois
extension, a perfect field, or a characteristic assumption. Selecting an index
now gives an actual finite separable stabilizer field. Descending the selected
factor and identifying a Weil restriction remain separate obligations for the
classification theorem.
