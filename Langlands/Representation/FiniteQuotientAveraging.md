# Averaging over a finite quotient

This is internal representation-theoretic infrastructure for the sufficient
direction of Nagata's theorem. Let `N` be a normal subgroup of an abstract group
`G`. If `G/N` is finite and its order is invertible in a commutative coefficient
ring, an `N`-fixed vector can be averaged over `G/N` to produce a `G`-fixed
vector. The formula is independent of the choice of coset representatives.
The average stays in any subrepresentation containing the original vector.

The construction uses Mathlib's action of `G/N` on the `N`-invariants and its
finite-group averaging map. The displayed coset-section formula follows by
expanding the group-algebra average. Subrepresentation membership follows because
each translate belongs to the same subrepresentation.

The motivating source is J. S. Milne, *Algebraic Groups*, corrected reprint (2022),
Exercise 4-3, printed p.97, and the averaging argument in the proof of Corollary
22.43, printed p.479. The latter passage occurs in characteristic zero; this
internal abstraction instead explicitly assumes that the quotient order is
invertible. The official errata snapshot of 4 November 2026 has no correction to
these passages. This module makes no assertion about a group scheme's identity
component or its component group.
