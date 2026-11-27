# Group operations used in the simple-character commutator calculation

The group manipulations here implement the decompositions and commutator bounds of Bushnell–Kutzko (1993), (3.1.14)–(3.1.15), printed p. 95 (PDF p. 107), and the use of commutator identities in (3.2.6)–(3.2.12), printed pp. 100–103 (PDF pp. 112–115). The registered source `bushnell-kutzko-1993-admissible-dual-gln` has SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.

For a level-zero simple stratum with a supplied defining sequence, `commutator_mem_HGroup` applies the simple-stratum subgroup properties at positive depths `k,l`. It takes the commutator of two individual representatives in `J^k` and `J^l`, then uses monotonicity of `H` to place it in `H^p` for `p ≤ k+l`.

For a subgroup `H` of a group `G` and a character `χ : H →* ℂˣ`, `character_commutator_mul_mul` evaluates the commutator of two products. The first factor in each product normalizes the character. Evaluations of the conjugated commutators are therefore the evaluations of those commutators, and the three terms involving either first factor are discarded when their evaluations equal one. Reversing a commutator inverts its evaluation.
