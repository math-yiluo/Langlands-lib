# Powers in the actual integral-model congruence tower

This internal construction applies square-zero coefficient powers to the
published actual congruence tower of an integral group model, at arbitrary
universe `u`.

For a commutative local ring `R`, `congruenceTransitionAlgHom R h` is the
existing quotient map from `R / m^k` to `R / m^n`, bundled as an algebra map
over `R`, where `m` is the actual maximal ideal and `h : n ≤ k` relates positive
levels. The underlying function is exactly `congruenceRingTransition R h`.
If `k ≤ n + n`, its kernel is square-zero. If a natural number `p`, viewed in
`R`, belongs to `m`, it annihilates the kernel of the transition from level
`n + 1` to level `n`.

For an `IntegralModel R K G`, `congruenceAffinePointsEquiv M n` identifies the
points of its actual level-`n` fibre with coefficient points of the original
model over `R / m^n`. This is the existing group-valued pullback point
equivalence. The transition comparison proves that it carries
`M.congruenceTransition h` to `Lie.affineMap` for the same quotient algebra map.

Consequently `pow_mem_congruenceKernelAt_succ` proves
`x ∈ M.congruenceKernelAt n → x ^ p ∈ M.congruenceKernelAt (n + 1)` under
`(p : R) ∈ m`. `pow_mem_congruenceSubgroupAt_succ` gives the identical
conclusion for the actual generic-point image `M.congruenceSubgroupAt`.
The two `pow_pow_mem_...` lemmas iterate this: `x ^ (p ^ j)` belongs to the
level whose natural-number value is `n + j`. The actual residue characteristic
belongs to `m`, as recorded by `residueChar_mem_maximalIdeal`.

The coefficient proofs lift elements to the original ring and use
`m^n * m^n = m^(n+n)` and `m * m^n = m^(n+1)`. The point proof applies
`Lie.affineKernel_pow_eq_one` to the coefficient transition and transports its
conclusion through the pullback equivalence. The generic-point proof uses the
original integral-point homomorphism; induction proves the iterated claims.
No smoothness, prime characteristic, finite residue field, or topological
hypothesis is imposed. Here `p` is any natural number satisfying the stated
maximal-ideal condition. This unit does not assert a pro-`p` conclusion; that
also requires the topological neighborhood-basis argument.

The provenance is internal: it combines the actual quotient coefficients and
point restrictions from `IntegralModel.CongruenceTower` with the affine
square-zero group-point power result from `InfinitesimalPowers`.
