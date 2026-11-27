# Descent of a character evaluated on commutators

The construction in `exists_quotientCommutatorPairing` is the group argument in the opening paragraph of Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), Theorem (3.4.1), printed p. 115 (PDF p. 127). The registered source `bushnell-kutzko-1993-admissible-dual-gln` has SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.

The hypotheses are `H ≤ J`, membership of the commutators of `J` in `H`, and an equality of the left annihilator of commutator evaluation with `H`. The first two give normality of `H` in `J` using `x h x⁻¹ = [x,h] h`. Reversal of the commutator turns left annihilation by `H` into right annihilation. The conjugation identity then gives invariance of the character under `J`.

Evaluating the two commutator product identities with the character gives a homomorphism in each argument. The quotient map on `J` has kernel `H.comap J.subtype`. The two annihilation identities allow a quotient lift in each argument, and surjectivity of the quotient map transfers alternation and the left annihilator condition to the actual quotient. The construction uses no finiteness of either group.
