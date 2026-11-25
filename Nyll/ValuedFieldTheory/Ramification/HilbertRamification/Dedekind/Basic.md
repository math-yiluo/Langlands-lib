# Decomposition and inertia groups of primes in Dedekind extensions

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.Basic`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file gives the prime-ideal form of Hilbert ramification theory. A group `G` acts on a ring `B` that is an `A`-algebra; for a prime `P` of `B` over `p` of `A`, the decomposition group is the stabilizer of `P` and the inertia group the elements acting trivially on `B/P`. The file proves the residue exact sequence, the orbit description of the primes over `p`, and the cardinality formulas `|G_P| = e·f`, `|I_P| = e`.

## Definitions

- `decompositionGroup P G`: the stabilizer of `P` (`σ • P = P`).
- `inertiaGroup P G`: Mathlib's inertia subgroup, `σx − x ∈ P` for all `x`.
- `residueStabilizerHom p P G`: Mathlib's `Ideal.Quotient.stabilizerHom`, the map from `G_P` to `(A/p)`-algebra automorphisms of `B/P`, `b mod P ↦ σb mod P`; it requires the action to commute with `A`-scalars (`SMulCommClass G A B`).

## Main results

- `inertiaSubgroupOfDecomposition_normal`: `I_P` is normal in `G_P`, proved by conjugation.
- Residue sequence: `dedekindRamification_residueAction_ker` (kernel is `I_P`), `dedekindRamification_residueAction_mulExact`, `dedekindRamification_residueAction_surjective` (finite `G`, `A → B` invariant under `G`), `dedekindRamification_residueAction_shortExact`, and `dedekindRamification_decompositionQuotientInertiaEquivResidueGalois`: `G_P/I_P ≃* Aut(B/P over A/p)`. For `p` and `P` maximal, `G` finite and `A → B` invariant under `G`, the residue extension is normal, and Galois when separable.
- Trivial inertia: the residue action is then bijective, giving `G_P ≅ Aut(B/P over A/p)` and an injective homomorphism from it into `G`.
- For a finite Galois group `G` of `B/A` (`IsGaloisGroup G A B`): transitivity on primes over `p`; `e` does not depend on `P`, nor does `f` when `p` is maximal; `dedekindDecomposition_primesOverEquivQuotientDecompositionGroup`: primes over `p` ≃ `G/G_P`; their number is the index of `G_P`; `G_P = G` iff there is one prime, and `G_P = 1` iff there are `|G|` primes; `r·|G_P| = |G|`.
- With `A`, `B` Dedekind, `B` finite and torsion-free over `A`, `p` maximal and nonzero: `dedekindRamification_galois_prime_decomposition` (`pB = ∏ P^e`), `dedekindRamification_galois_fundamental_identity` (`r·e·f = |G|`), its unramified forms `r·f = |G|` and `r = |G|/f`, and `|G_P| = e·f`.
- With separable residue extension: `|G_P/I_P| = f`, `|G_P| = |I_P|·f`, and `dedekindRamification_inertia_card_eq_ramificationIdxIn`: `|I_P| = e`.

## Proofs

Most statements restate Mathlib's results on `stabilizerHom`, Galois groups of ring extensions and `ramificationIdxIn`/`inertiaDegIn`. The cardinality of `I_P` comes from comparing `|G_P| = |I_P|·f` with `|G_P| = e·f`.

## Points to watch

- The formulas `|G_P/I_P| = f` and `|I_P| = e` assume that `B/P` is separable over `A/p`.
- "Galois" means a finite group `G` with `IsGaloisGroup G A B`, not a field extension; the residue "Galois group" is the full automorphism group of `B/P` over `A/p`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/Dedekind/Basic.lean`: the Lean file is the source byte for byte (SHA-256 `5f55d2d72e76ce088eb733b51d1efe00321d9c6d909fe16537448e16788236a3`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
