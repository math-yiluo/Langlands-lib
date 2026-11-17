# Extending semisimplicity across a finite normal quotient

For representations of an abstract group over a field, semisimplicity extends
from a normal subgroup `N` whenever `G/N` is finite and its order is invertible
in the field. The theorem `isSemisimpleRepresentation_of_normalRestriction`
states this with a chosen finite enumeration and an invertibility instance.
The theorem `isSemisimpleRepresentation_of_primeToNormalQuotient` states the
characteristic-`p` version using `¬ p ∣ Nat.card (G/N)` and a `Finite` instance.
Neither theorem needs finite dimensionality.

The auxiliary construction `projectionOfIsCompl` is the equivariant projection
along two complementary subrepresentations, over any commutative ring.
Its equivariance follows from Mathlib's criterion that an idempotent commutes
with an operator exactly when its image and kernel are invariant. Its image and
kernel are the two prescribed summands.

For semisimplicity, restrict a `G`-stable subspace to `N` and choose an
`N`-stable complement. Its projection is `N`-equivariant. Averaging that
projection over `G/N` makes it `G`-equivariant while preserving both projection
properties. The averaged map's kernel is the required `G`-stable complement.
The characteristic-`p` corollary converts the nondivisibility hypothesis to
nonvanishing of the cardinal's image in the field and hence to invertibility.

This is an internal abstract-group form of the averaging step in J. S. Milne,
*Algebraic Groups*, corrected reprint (2022), Exercise 4-3, printed p.97, and the
proof of Corollary 22.43, printed p.479. The latter passage assumes characteristic
zero; the Lean result states the precise quotient-order hypothesis. The official
errata snapshot of 4 November 2026 has no correction to these passages.
Applying this result to group schemes still requires the all-test stability
comparison and the identification of the finite geometric component quotient.
