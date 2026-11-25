# Infinite upper ramification under restriction and isomorphism

Module `FontaineWintenberger.Ramification.Infinite.Restriction`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field in the library's sense. The file proves that the infinite upper ramification groups `upperRamificationGroupInfinite K Ω u` are compatible with restriction to a Galois intermediate field `L` of `Ω`, including surjectivity, and with `K`-isomorphisms of fields. All statements are for real `u ≥ −1`.

## Definitions

Auxiliary constructions, for arbitrary fields:

- `finiteGaloisLift L E`: a finite Galois intermediate field `E` of `L/K` regarded as a finite Galois intermediate field of `Ω/K`; `finiteGaloisLiftEquiv L E` is the isomorphism from `E` onto it.
- `finiteGaloisMap K f D`: the image of a finite Galois intermediate field `D` of `L/K` under a `K`-algebra map `f : L → M`; `finiteGaloisMapEquiv K f D` is the isomorphism from `D` onto it.

## Results

- `restrictNormal_finiteGaloisLift`, `restrictNormal_finiteGaloisMap`: restriction of automorphisms commutes with these isomorphisms.
- `restrictNormal_mem_upperRamificationGroupInfinite`: for `L/K` Galois inside `Ω`, if `s` lies in the upper group of `Ω/K` at `u`, then `s.restrictNormal L` lies in that of `L/K`.

With `Ω/K` Galois and the residue field of `K` perfect:

- `exists_lift_finite_infinite_upper_restrictions`: for `q` in the upper group of `L/K` and a finite set `S` of finite Galois subextensions of `L`, some `s` in the upper group of `Ω/K` agrees with `q` on every `E ∈ S`.
- `exists_lift_infinite_upper_restriction`: every `q` in the upper group of `L/K` is the restriction of an element of the upper group of `Ω/K`.
- `restrictNormalHom_map_upperRamificationGroupInfinite`: the image of `upperRamificationGroupInfinite K Ω u` under restriction to `L` equals `upperRamificationGroupInfinite K L u`.

For a `K`-algebra isomorphism `f : L ≃ₐ[K] M` of arbitrary extensions:

- `mem_upperRamificationGroupInfinite_autCongr_iff`: `f.autCongr s` lies in the upper group of `M/K` if and only if `s` lies in that of `L/K`.
- `upperRamificationGroupInfinite_map_autCongr`: transport by `f` maps the upper group of `L/K` onto that of `M/K`.

## Proofs

The finite upper groups are invariant under isomorphism (`upperRamificationGroup_map_autCongr`, from an earlier file), which handles the passage between `E` and its copy in `Ω`. The finite lifting statement reduces to the compositum of the fields in `S` and uses `exists_lift_upperRamificationGroupInfinite` from the basic file on infinite extensions. The full lifting follows from compactness of the upper group of `Ω/K`.

## What to watch for

- `L` here is an `IntermediateField K Ω`; the versions for a subextension given as a separate field in a scalar tower are in other files.
- Containment under restriction needs only `L/K` Galois; surjectivity needs `Ω/K` Galois and a perfect residue field.
- The isomorphism statements make no Galois assumption on `L` or `M`.

## References

Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Infinite/Restriction.lean` (SHA-256 of the source file `42edf81dd09cae74bfe8ffad513f615d28bcad9823c6aff8b09e7f151d8c7bfb`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
