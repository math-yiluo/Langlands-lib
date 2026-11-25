# The radical extension K(ⁿ√Δ)

Module `Nyll.GaloisCohomology.Kummer.Concrete.RadicalExtension`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a field `K`, a separable closure `Ω` of `K` and a subgroup `Δ ≤ Kˣ`, the file builds the field obtained by adjoining to `K` every root in `Ω` of every equation `β^n = a` with `a ∈ Δ`, and proves that it is Galois over `K`, and abelian of exponent dividing `n` when `K` contains a primitive `n`-th root of unity. Adjoining all roots, rather than chosen ones, makes the field independent of choices and stable under `Gal(Ω/K)`.

## Main definitions

- `unitNthPowersSubgroup K n`: the subgroup `Kˣⁿ` of `n`-th powers of units.
- `KummerSubgroup K n`: subgroups `Δ ≤ Kˣ` containing `Kˣⁿ`, as a subtype.
- `kummerRootSet n Δ`: all `β ∈ Ω` with `β^n ∈ Δ` (as an element of `Kˣ`).
- `kummerRadicalExtension n Δ`: the intermediate field of `Ω/K` they generate, written `K(√[n]{Delta})`.

## Main results

- `exists_kummerRootSet`: if `(n : K) ≠ 0`, every `a ∈ Δ` has an `n`-th root in `Ω`, since `X^n − a` is separable.
- `le_finiteKummerRadicalSubgroup_kummerRadicalExtension`: if `(n : K) ≠ 0`, every element of `Δ` has an `n`-th root in `K(ⁿ√Δ)`; `unitNthPowersSubgroup_le_constructedRadical` records that, when `Δ` is a `KummerSubgroup` (so contains `Kˣⁿ`), the radical subgroup of the constructed field still contains `Kˣⁿ`.
- `kummerRadicalExtension_map`, `kummerRadicalExtension_normal`, `kummerRadicalExtension_isGalois`: every `σ ∈ Gal(Ω/K)` maps the root set onto itself, so the field is normal, and Galois over `K`.
- `kummerRadicalExtension_isMulCommutative`, `kummerRadicalExtension_galois_pow_eq_one`: with a primitive `n`-th root of unity in `K`, the Galois group is commutative and every element has `n`-th power `1`.
- `kummerRadicalExtension_isAbelianGalois`: the forward construction of the Kummer correspondence; the extension is abelian Galois.

## Proofs

Commutativity and the exponent bound are checked on the radical generators: for a root `β`, `σ(β)/β` is an `n`-th root of unity, hence lies in `K` under the primitive-root hypothesis and is fixed by every automorphism. Separability comes from the ambient separable closure.

## Points to watch

- The Galois property needs only `Ω` to be a separable closure; `(n : K) ≠ 0` (n prime to the characteristic) enters only to guarantee that each `a ∈ Δ` has an `n`-th root in `Ω`.
- Finiteness of the extension is not claimed here.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Kummer/Concrete/RadicalExtension.lean`: the Lean file is the source byte for byte (SHA-256 `c76351eace5db395a1e7aa70ad87ca9c2b76bb6ceb0eddcf56361a31f5d5447a`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
