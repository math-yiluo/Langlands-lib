# The `p`-adic degree comparison from four inputs

This module defines a reduction proposition and proves it.

## The proposition

`Langlands.AbelianScheme.IsogenyDegreeTateDeterminantNormReductionStatement` is the implication

`IsogenyFinrankKernelCardStatement.{u} → IsogenyKernelCardTateDeterminantStatement.{u} → TateDeterminantNonzeroSurjectiveStatement.{u} → FieldSurjectiveEndomorphismIsogenyStatement.{u} → IsogenyDegreeTateDeterminantNormStatement.{u}`.

All five propositions are in `Langlands/AbelianScheme/`:

- `IsogenyFinrankKernelCardStatement`: in characteristic zero, the rank of an isogeny at every point is the number of `k`-points of its kernel.
- `IsogenyKernelCardTateDeterminantStatement`: for `(p : k) ≠ 0`, the number of `k`-points of the kernel of an isogeny and the determinant of its rational `p`-adic Tate map have the same `p`-adic norm.
- `TateDeterminantNonzeroSurjectiveStatement`: in characteristic zero, a nonzero Tate determinant makes the endomorphism surjective.
- `FieldSurjectiveEndomorphismIsogenyStatement`: a surjective endomorphism is an isogeny.
- `IsogenyDegreeTateDeterminantNormStatement`: the target, in characteristic zero.

## Proof

`isogenyDegreeTateDeterminantNormReduction` proves it. Fix `k`, `A`, a prime `p` and `α`. In characteristic zero, `(p : k) ≠ 0`.

- If `α` is an isogeny, the first input rewrites the rank at `y` as the number of kernel points, and the second input gives the norm equality.
- If `α` is not an isogeny and the determinant were nonzero, the third input would make `α` surjective and the fourth would make it an isogeny. So the determinant is `0`.

## Provenance

Internal reduction between Library propositions. It splits the chain in the proof of Milne, *Abelian Varieties* (author revision 2022), Proposition 12.9, p. 23, into its geometric steps.
