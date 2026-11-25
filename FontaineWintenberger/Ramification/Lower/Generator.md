# Computing ramification on an integral generator

Module `FontaineWintenberger.Ramification.Lower.Generator`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

When `S` is generated over `R` by one element `x`, inertia and ramification order are read off from `g • x − x`.

For a group `G` acting on `S` by ring automorphisms commuting with `R`, and `Algebra.adjoin R {x} = ⊤`:

- `mem_inertia_iff_generator`: `g ∈ I.inertia G` if and only if `g • x − x ∈ I`, for any ideal `I` of `S`.
- `ramificationOrder_eq_generator`: if `S` is a discrete valuation ring, `ramificationOrder G g = addVal S (g • x − x)`.
- `mem_lowerRamificationGroup_iff_generator`: `g ∈ G_n` if and only if `(n + 1).toNat ≤ addVal S (g • x − x)`.

For `K` complete discretely valued with perfect residue field and `L/K` finite separable:

- `spectralIntegerRing_exists_order_generator`, `spectralIntegerRing_exists_galois_order_generator`: some `x` in `spectralIntegerRing K L` computes the order of every element of the decomposition subgroup, respectively of `L ≃ₐ[K] L`.

## What to watch for

The general statements take the generator as a hypothesis; the last two obtain one from `spectralIntegerRing_exists_generator`, proved elsewhere.

## References

Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Lower/Generator.lean` (SHA-256 of the source file `3ef74ce0f06e4d8d2c75245ecfd62f7f9ef75b3e5cb026eb56188b0eb4eccce0`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
