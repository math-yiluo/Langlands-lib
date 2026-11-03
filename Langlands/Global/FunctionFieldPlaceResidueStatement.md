# Finite residue extensions at actual function-field places

`Langlands.Global.FunctionFieldPlaceResidueStatement` asserts that every actual
curve place of a function field has residue field finite dimensional over the
constant field.

The inputs are fields `k` and `F` in the same arbitrary universe, the given
`k`-algebra structure on `F`, a `RatFunc k`-algebra structure on `F`, their
compatible scalar tower, and `FunctionField k F`. The latter means that `F` is
finite dimensional over the specified rational-function field. For every
`v : AlgebraicCurve.Place k F`, the conclusion is
`Module.Finite k v.ResidueField`. This is module finiteness for the existing
constant-field action on the actual quotient of `v.toValuationSubring` by its
maximal ideal. Over the field `k`, it is equivalent to finite dimensionality.

Neither perfectness of `k` nor separability of the specified presentation is
assumed. The conclusion is finite dimensionality over `k`; a finite cardinality
conclusion follows when the constant field is finite. The existing place type
consists of proper principal valuation subrings containing the constant field.
`FunctionFieldValuationPlaces` proves that the principal-ideal property is
automatic for such valuation subrings in the stated function-field setting.

This is a derived arithmetic prerequisite for the function-field part of the
Conrad adelic-point program, rather than a direct transcription of a separately
numbered assertion in the paper. The proposed proof uses the published
Krull–Akizuki overring theorem and Mathlib's Zariski lemma. It does not assume
residue finiteness as structure data. This statement defines the proof target;
it does not itself prove it or assert compactness of local completions,
discreteness of the adelic diagonal, or any geometric point comparison.
