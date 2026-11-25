# Artin images of principal units and the conductor

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.Core`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite abelian extension `L / K` of a nonarchimedean local field, the local Artin map `Kˣ → Gal(L / K)` carries the principal-unit filtration `U_K^(n)` to a filtration of the Galois group. Filtered local reciprocity identifies this filtration with the upper ramification filtration. This file develops the Artin side only: the filtration, its real-indexed step version, its behaviour under restriction, and its cutoff at the conductor. The comparison itself is not proved here; the descent lemma takes it as a hypothesis.

## Main definitions and results

- `Universe.abelianLocalArtinMonoidHom_restrict`: for finite abelian `E ≤ F` inside `SeparableClosure K`, restriction from `Gal(F / K)` to `Gal(E / K)` composed with the Artin map of `F` is the Artin map of `E`.
- `artinPrincipalUnitGroup K L n`: the image of `fieldPrincipalUnits K n` under `Universe.abelianLocalArtinMonoidHom K L`. For `K, L : Type` it equals the image under `abelianLocalArtinMonoidHom K L` (`artinPrincipalUnitGroup_eq_nativeArtinImage`). It is antitone in `n`.
- `artinPrincipalUnitGroup_eq_bot_iff` and `artinPrincipalUnitGroup_ne_bot_iff`: the image is trivial exactly when `localConductorExponent K L ≤ n`. Proof: the kernel of the Artin map is the norm subgroup (`Universe.abelianLocalArtinMonoidHom_ker`), combined with `localConductorExponent_le_iff`.
- `artinPrincipalUnitGroup_map_intermediateFieldRestrict`: restriction carries the image for `F` onto the image for `E`.
- `artinPrincipalUnitStepGroup K L t`: the real-indexed filtration built by `natCeilStepFiltration`; it is the image of `U_K^(⌈t⌉₊)` (`artinPrincipalUnitStepGroup_eq_nativeArtinImage`) and is compatible with restriction.
- `filteredLocalReciprocity_descends`: given families `upperE`, `upperF` of subgroups compatible with restriction (`hupper`), and equality of the Artin step filtration of `F` with `upperF` at all `t ≥ 0` (`hcover`), the same equality holds for `E` at `t ≥ 0`.
- `IsArtinPrincipalUnitJump`: jumps of the step filtration. `isArtinPrincipalUnitJump_natCast_iff`: there is a jump at a natural number `n` exactly when the images at `n` and `n + 1` differ. `isArtinPrincipalUnitJump_integer`: every jump is a natural number. `exists_lastArtinPrincipalUnitJump_of_conductor_pos`: if the conductor exponent is `n + 1 > 0`, there is a jump at `n`.

## Points to watch

- The comparison with upper ramification groups is a hypothesis wherever it appears: `filteredLocalReciprocity_descends` assumes it for `F` (`hcover`) and assumes compatibility of the chosen upper filtrations with restriction (`hupper`).
- The step filtration uses the natural ceiling `⌈t⌉₊`, so every `t ≤ 0` gives the image of `U_K^(0)`. The index `-1` lies outside this comparison; a docstring says it is handled separately in the Hasse–Arf development.
- The conductor exponent counts from `U_K^(0)`, so, when the conductor exponent is positive, there is a jump at one less than it.
- Most results allow `K` and `L` in arbitrary universes through the universe-independent Artin map; the comparisons with the native Artin map take `K, L : Type`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/Filtered/Core.lean`: the Lean file is the source byte for byte (SHA-256 `f2c15953d496b46274a85a7aeee91806b6dc76e5a0175f8dfe7cf970233e9e84`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
