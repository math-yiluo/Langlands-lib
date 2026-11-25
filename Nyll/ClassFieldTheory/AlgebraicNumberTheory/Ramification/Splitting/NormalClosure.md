# Complete splitting and normal closures

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.NormalClosure`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `M/K` be a finite Galois extension with group `G`, `L` an intermediate field with `H = Gal(M/L)`, `v` a nontrivial absolute value of `K`, and `w` an extension of `v` to `M` with decomposition group `D`. The extensions of `v` to `L` correspond to the double cosets `H \ G / D`. This file uses this to define complete splitting for non-Galois extensions, and shows that a place splitting completely in `L` splits completely in the normal closure of `L`.

## Main definitions and results

- `doubleCosetExtensionEquiv`: the bijection `H \ G / D ≃ {extensions of v to L}`, sending the class of `g` to the restriction of the conjugate of `w` by `g⁻¹` (`doubleCosetExtension`, with `_surjective` and `_injective`).
- `AbsoluteValueSplitsCompletelyInExtension v` (for `E/K` finite): the number of absolute values on `E` extending `v` equals `[E : K]`; `FinitePlaceSplitsCompletelyInExtension v` specializes it to the `v`-adic absolute value of a number field.
- `absoluteValueSplitsCompletelyInExtension_iff_doubleCoset_card_eq`: `v` splits completely in `L` iff `|H \ G / D| = |H \ G|`, the latter being `[L : K]` (`leftCosetDoubleCoset_card_eq_finrank`).
- `absoluteValueDecompositionGroup_eq_bot_of_splitsCompletelyInIntermediate`: if `H` has trivial normal core and `v` splits completely in `L`, then `D = 1`.
- `fixingSubgroup_normalCore_eq_bot_of_normalClosure_eq_top`: if the `K`-conjugates of `L` generate `M`, then `H` has trivial normal core.
- `finitePlaceSplitsCompletely_in_normalClosure`: for a finite place `v` of a number field `K`, if `v` splits completely in `L` (intrinsic sense) and `M` is the normal closure of `L`, then `v` splits completely in `M` (decomposition-group sense).
- `finitePlaceSplitsCompletely_iff_inExtension`: for `E/K` Galois, the two senses agree; `finitePlaceSplitsCompletelyInExtension_algEquiv`: the intrinsic one is invariant under `K`-isomorphism.
- `finitePlaceSplitsCompletely_of_decompositionGroup_le_restrictNormalHom_ker`: for `K ⊆ E ⊆ N` with `E/K` finite Galois and `N/K` Galois, if the decomposition group in `N` acts trivially on `E`, then `v` splits completely in `E`.
- For the library's `finiteNormalClosure K L`: `finite_nonSplittingPlaces_normalClosure_of_original` shows that if almost all finite places split completely in `L`, the same holds in the closure.

## Proof

The double-coset bijection rests on the imported conjugacy of extensions of an absolute value in a Galois extension, applied over `K` and over `L`. Passing from equal coset counts to `D = 1` for core-free `H` is an imported group-theoretic lemma.

## Points to watch

- Two notions of complete splitting appear: `FinitePlaceSplitsCompletely`, triviality of the decomposition group of a chosen extension (Galois case), and the intrinsic count `FinitePlaceSplitsCompletelyInExtension`. The bridge needs `E/K` Galois.
- Extensions are counted as absolute values on `E` restricting exactly to `v`, not as places up to equivalence.
- The double cosets are oriented as `H \ G / D` by the inversion `g ↦ g⁻¹`, not in the convention `D \ G / H`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Ramification/Splitting/NormalClosure.lean`: the Lean file is the source byte for byte (SHA-256 `d3806c94ab6cb9b7765345c280107d40802b9a91e386b233c01bf3196402c63a`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
