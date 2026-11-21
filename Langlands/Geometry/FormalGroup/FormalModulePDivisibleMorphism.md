# Formal module maps on their p-divisible groups

An integral formal module map induces `Hom.pDivisibleMap` by restricting
to the actual kernels of all powers of `p`. The restrictions commute with
the inclusions and the multiplication transfers. Identity and composition
follow from the corresponding restrictions to each represented kernel.

Restriction preserves addition. On an affine test, the base-changed formal
maps are additive in the morphism variable. The equivalence with actual
finite scheme points transports this addition to the group scheme map.
The resulting endomorphism ring map transports an order action by
`OrderAction.pDivisibleAction`.

This is the morphism construction for the passage from a divisible formal
Lie group to its torsion tower in Tate, *p-Divisible Groups* (1967), §2.2,
printed p. 162 (PDF p. 3), before and in the proof of Proposition 1. Here
the input consists of an actual formal module and the scalar-divisibility
conditions that supply its finite kernel models.
