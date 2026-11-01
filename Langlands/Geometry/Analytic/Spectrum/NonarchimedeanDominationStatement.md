# Multiplicative domination of an ultrametric ring seminorm

`Langlands.Analytic.BanachSpectrum.NonarchimedeanDominationStatement`
asserts that a ring seminorm `p` on a commutative ring `A : Type u` satisfying
`p 1 = 1` and the strong triangle inequality dominates a multiplicative ring
seminorm `q` satisfying the strong triangle inequality. Domination is pointwise:
`q a ≤ p a` for every `a`. The normalization `q 1 = 1` belongs to
Mathlib's `MulRingSeminorm` structure.

This is an internal auxiliary statement for the common complete-field
realization of compatible affinoid points. Its formulation isolates the
seminorm-existence step before any topology or completion on the ring is
chosen. The statement does not assume that `A` is a domain, a field, a normed
algebra, or complete. Normalization already excludes the zero ring; no
additional nonzero hypothesis is imposed. The universe is arbitrary.

The intended application takes `p` to be a normalized ultrametric norm on an
algebraic tensor product. Its dominated multiplicative seminorm can then be
used to form a completed residue field. This file states the auxiliary
existence result; it does not prove the tensor construction or point
amalgamation.
