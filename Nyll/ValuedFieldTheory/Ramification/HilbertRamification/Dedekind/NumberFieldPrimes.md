# Ramification indices and residue degrees in the tower K ⊆ Z_P ⊆ T_P ⊆ L

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.NumberFieldPrimes`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be an extension of number fields with finite Galois group `G` (`IsGaloisGroup G K L`), `P` a maximal ideal of `𝓞_L`, `p` the prime of `𝓞_K` below it (`basePrime`), and `P_Z`, `P_T` the primes below `P` in the decomposition field `Z_P` and inertia field `T_P` (`decompositionFieldPrime`, `inertiaFieldPrime`). The file computes the ramification indices and residue degrees at each step of the tower: `P_Z/p` has `e = f = 1`, `P_T/P_Z` has `e = 1` and residue degree `f`, and `P/P_T` has `e(P|p)` and residue degree `1`.

## Main results

- `dedekindTower_decompositionFieldPrime_primesOver_ncard_eq_one`, `dedekindRamification_inertiaFieldPrime_primesOver_ncard_eq_one`: `P` is the only prime of `𝓞_L` above `P_Z`, and above `P_T`.
- `dedekindTower_decompositionFieldPrime_product_eq_base_product`: `e(P|P_Z)·f(P|P_Z) = e(P|p)·f(P|p)`, both being `|G_P|`.
- `dedekindTower_decompositionFieldPrime_tower_invariants`: `e(P_Z|p) = f(P_Z|p) = 1`, `e(P|P_Z) = e(P|p)` and `f(P|P_Z) = f(P|p)`.
- With `(𝓞_L/P)/(𝓞_K/p)` separable:
  - `dedekindRamification_inertiaFieldPrime_residue_isSeparable`: separability passes to `P/P_T` (this lemma needs no number-field hypothesis);
  - `dedekindRamification_inertiaFieldPrime_inertiaDeg_eq_one` and `dedekindRamification_inertiaFieldPrime_top_invariants`: `f(P|P_T) = 1` and `e(P|P_T) = e(P|p)`;
  - `dedekindRamification_inertiaFieldPrime_middle_invariants`: `e(P_T|P_Z) = 1` and `f(P_T|P_Z) = f(P|p)`;
  - `dedekindRamification_inertiaField_degree_cardinalities`: `|I_P| = [L : T_P] = e` and `|G_P/I_P| = [T_P : Z_P] = f`;
  - `dedekindRamification_inertiaFieldPrime_tower_invariants`: the four invariants of the two upper steps together;
  - `inertiaGroup_eq_bot_iff_isUnramifiedAt` and `dedekindRamification_inertiaField_eq_top_iff_isUnramifiedAt`: `I_P = 1`, equivalently `T_P = L`, iff `P` is unramified over `𝓞_K` in the sense of `Algebra.IsUnramifiedAt`.

## Proofs

Over `Z_P` (and over `T_P`) the group `G_P` (resp. `I_P`) is a Galois group of the rings of integers with a single prime above, so `e·f` equals its order. Comparing with `|G_P| = e·f` and `|I_P| = e` over `K`, and using multiplicativity of `e` and `f` in towers from the companion files, gives the step-by-step values. `f(P|P_T) = 1` holds because inertia over `T_P` is all of `I_P`.

## Points to watch

- Separability of the residue extension is an instance hypothesis on the `T_P` statements other than the uniqueness of the prime above `P_T`; the file does not derive it from finiteness of the residue fields.
- Several statements use the variant `Ideal.ramificationIdx'`, related to `Ideal.ramificationIdx` for nonzero primes.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/Dedekind/NumberFieldPrimes.lean`: the Lean file is the source byte for byte (SHA-256 `01370ce9821d8d7f6bd55371421f70b5e5d8112b6c893d12ff24fefaa83f8f16`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
