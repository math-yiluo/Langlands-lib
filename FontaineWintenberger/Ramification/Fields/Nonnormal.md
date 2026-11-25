# Ramification indices of fixed fields of arbitrary subgroups

Module `FontaineWintenberger.Ramification.Fields.Nonnormal`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field (in the library's sense) with perfect residue field, `L/K` finite Galois with group `G`, `B = spectralIntegerRing K L`, `D` the zeroth lower ramification group (inertia) and `P` the first (wild inertia). For a subgroup `H` of `G`, not assumed normal, the file computes the ramification index of the fixed field `L^H` over `K` and studies its compositum with the tame fixed field `L^P` when `L^H/K` is totally ramified of `p`-power degree.

The integers of `L^H` are the valuation ring of the spectral valuation of `L` restricted to `L^H`.

## Results

- `fixedField_ramificationIdx_eq_relIndex`: the ramification index of `L^H` over `K` equals `H.relIndex D`, that is `[D : H ⊓ D]`.
- `fixedField_sup_inertia_eq_top`: if this index equals `[L^H : K]`, then `H ⊔ D = ⊤`.
- `fixedField_ramificationIdx_eq_finrank_iff`: `L^H/K` is totally ramified (index equal to degree) if and only if `H ⊔ D = ⊤`.

The next four take a prime `p` that is the characteristic of the residue field of `B`, and assume that `L^H/K` is totally ramified of degree `p ^ n`:

- `fixedField_sup_wild_eq_top`: `H ⊔ P = ⊤`.
- `fixedField_wild_linearDisjoint`: `L^P` and `L^H` are linearly disjoint over `K`.
- `fixedField_wild_compositum_finrank`: the compositum `L^P ⊔ L^H` has degree `[L^H : K]` over `L^P`.
- `fixedField_wild_norm_baseChange`: for `x ∈ L^H`, the norm of `x` from the compositum to `L^P` is the image in `L^P` of the norm of `x` from `L^H` to `K`.

## Proofs

The first result combines the multiplicativity of ramification indices in the tower `𝒪[K] ⊆ 𝒪(L^H) ⊆ B` with the facts that `|D|` is the ramification index of `L/K` and `|H ⊓ D|` that of `L/L^H`. The equivalence with `H ⊔ D = ⊤` is a count of indices, using normality of `D` (private group-theoretic lemmas). For the wild case, `[G : H]` is a power of `p` and the index `[D : P]` is prime to `p` (`wild_fixedField_ramificationIdx_coprime`, from the file on the tame fixed field), which forces `H ⊔ P = ⊤`. Linear disjointness follows because `L^P ⊓ L^H` is fixed by `H ⊔ P`; the norm statement is a private lemma on norms in a compositum of linearly disjoint fields.

## What to watch for

- "Totally ramified" is expressed as the equality of the ramification index with `Module.finrank K (L^H)`.
- The compositum is taken as `IntermediateField.extendScalars` over `L^P`, and elements of `L^H` are moved into it by an explicit subtype construction.
- The hypothesis on `p` is `CharP` of the residue field of `B`, so the residue characteristic is positive in those statements.

## References

Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Fields/Nonnormal.lean` (SHA-256 of the source file `7fb8e4ef5899262255c4fbffa616fa9b10685d574121e98ba5222538f7103f2f`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
