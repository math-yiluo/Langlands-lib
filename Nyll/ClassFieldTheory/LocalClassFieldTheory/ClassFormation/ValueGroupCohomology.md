# Tate cohomology of the value group ℤ with trivial Galois action

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.ValueGroupCohomology`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite extension `L / K` with Galois group `G = Gal(L / K)`, this file computes the Tate-style groups `H⁰` and `H⁻¹` of the value group `ℤ` (written multiplicatively as `Multiplicative Int`) with trivial `G`-action. These are the value-group factors of the local class field axiom: `#H⁰(G, ℤ) = |G|` and `H⁻¹(G, ℤ)` is trivial. The action is the library's `galoisGroupValueGroupMulDistribMulAction K L`, installed by a `let` inside each statement.

## Main results

- `galoisGroupValueGroup_tateNorm_toAdd`: the norm of `a ∈ ℤ` is `|G| · a`.
- `galoisGroupValueGroupFixedToZModHom`: reduction modulo `|G|` on the fixed subgroup, a homomorphism to `ℤ/|G|ℤ`. It is surjective (`galoisGroupValueGroupFixedToZModHom_surjective`) and its kernel is the norm subgroup (`galoisGroupValueGroupFixedToZModHom_ker`).
- `galoisGroupValueGroupHerbrandH0MulEquivZMod`: the isomorphism `H⁰(G, ℤ) ≃* ℤ/|G|ℤ`, obtained from the two facts above by the first isomorphism theorem.
- `galoisGroupValueGroupHerbrandH0Finite` and `galoisGroupValueGroup_herbrandH0_card`: `H⁰` is finite of cardinality `|G|`. With `[IsGalois K L]`, `galoisGroupValueGroup_herbrandH0_card_eq_finrank` gives cardinality `[L : K]`.
- `galoisGroupValueGroup_normKernelSubgroup_eq_bot`: the kernel of the norm is trivial, since `|G| · a = 0` forces `a = 0`.
- `galoisGroupValueGroupHerbrandHMinusOneFinite` and `galoisGroupValueGroup_herbrandHMinusOne_card_eq_one`: for every `σ ∈ G`, the group `H⁻¹` attached to `σ` is finite with exactly one element, deduced from the trivial norm kernel.

## Points to watch

- `HerbrandH0` and `HerbrandHMinusOne` are the library's own Tate-style groups from its Herbrand-quotient development, not Mathlib's group cohomology. `HerbrandHMinusOne` takes an element `σ` of `G` as an argument; the results here hold for every `σ`.
- `K` and `L` are arbitrary fields in one universe with `L` finite-dimensional over `K`; nothing local is assumed. Finiteness of `H⁰` and `H⁻¹` is derived, not assumed.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/ValueGroupCohomology.lean`: the Lean file is the source byte for byte (SHA-256 `fe5a9347010d5b05f1668f06466841e9b1e481381f8094f48427357f6aeb86d7`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
