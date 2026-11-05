# Chosen unit norm preimages under separable inertia valuation hypotheses

Author: Worker 1607.

This derived internal helper upgrades the published generic valuation hypotheses
`ReductionHyp` to surjectivity of the determinant unit norm for any finite
Galois extension. It imports the prime-power full norm helper.

For each prime, choose a Sylow subgroup and its fixed field. Prime-power full
norm surjectivity and norm transitivity show that every base unit raised to the
index of that Sylow subgroup lies in the full norm subgroup. That index is prime
to the chosen prime. Thus the order of a base unit's class in the quotient by
the norm subgroup has no prime divisor, so the class is trivial. The proof uses
the finite element order, whose value is allowed to be zero: if it were zero,
any prime would divide it, yielding the same contradiction. The separate
field-norm conclusion adds the zero case.

All valuation hypotheses remain explicit; this module does not construct
those hypotheses from a Henselian discrete base valuation.

`AmbientHyp.exists_reductionHyp` gives the explicit restriction from an
invariant real valuation on a possibly infinite Galois ambient field. It
reuses the construction in `AmbientHyp.exists_norm_eq_of_tower`: Galois
invariance descends simple-root Hensel lifting; algebraically closed residue
root finding gives residue approximation; norm values give discrete powers
of the original base uniformizer. The resulting
`AmbientHyp.surjective_unit_norm` proves full unit-norm surjectivity for every
finite Galois `M/E` embedded in that ambient field, with `E` finite over the
original base. All maps and scalar-tower instances are explicit.

The entry definition `AmbientHyp.unitNormSection` assigns to each unit of
`E` a unit of `M` by classical choice on this proved surjectivity theorem.
`AmbientHyp.norm_unitNormSection` proves that applying the actual
determinant unit norm to the assigned preimage returns the original unit.
