# Ramification indices and residue degrees in towers

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.TowerInvariants`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a tower of rings `A → B → C` and primes `p ⊆ P ⊆ Q` lying over one another, the file records multiplicativity of ramification indices and residue degrees, and two cancellation lemmas used to compute the invariants in the tower of decomposition and inertia fields.

- `ramificationIdx_tower` (`B`, `C` Dedekind, the relevant extended ideals nonzero, `PC ⊆ Q`): `e(Q|p) = e(P|p)·e(Q|P)`, for the variant `Ideal.ramificationIdx'`; a restatement of Mathlib's `Ideal.ramificationIdx'_algebra_tower`.
- `dedekindTower_inertiaDeg_tower` (`p`, `P` maximal): `f(Q|p) = f(P|p)·f(Q|P)`.
- `dedekindTower_tower_invariants_of_top_product`: for natural numbers with `e = e₁·e₂`, `f = f₁·f₂`, `e₂, f₂ ≠ 0` and `e₂·f₂ = e·f`, one gets `e₁ = f₁ = 1`, `e₂ = e`, `f₂ = f`. `dedekindTower_ideal_tower_invariants_of_top_product` is its ideal form, with `C` finite over `B`.
- `dedekindRamification_tower_middle_invariants_of_top_invariants`: with the same two product identities and `e₂ ≠ 0`, if `e₂ = e` and `f₂ = 1`, then `e₁ = 1` and `f₁ = f`; `dedekindRamification_ideal_tower_middle_invariants_of_top_invariants` is the ideal form.

In the ideal forms the hypothesis on the top layer (`e(Q|P)·f(Q|P) = e(Q|p)·f(Q|p)`, or the top invariants) is an explicit argument, to be supplied by the decomposition-field and inertia-field computations elsewhere.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/Dedekind/TowerInvariants.lean`: the Lean file is the source byte for byte (SHA-256 `87592ba8bf565c44d4d727d199f043c04876856d9b67de76eb5786e425c9c43d`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
