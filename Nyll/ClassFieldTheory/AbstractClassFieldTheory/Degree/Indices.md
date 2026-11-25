# Relative indices through a homomorphism

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Indices`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

A purely group-theoretic file. For a group homomorphism `d : G → D` and subgroups `L ≤ K` of `G`, the relative index `[K : L]` splits as the index of the images `[d(K) : d(L)]` times the index of the kernel parts `[K ∩ ker d : L ∩ ker d]`. The file proves this both for Mathlib's natural-valued `Subgroup.relIndex` and for cardinal-valued indices, and it is the index calculation behind the degree, residue degree and ramification index of abstract fields.

## Main definitions and results

- `kernelCosetEquivSaturation`: for `L ≤ K`, a bijection between the cosets of `L ∩ ker d` in `K ∩ ker d` and the cosets of `L` in `K ∩ (L ⊔ ker d)`. No normality of `L` is needed.
- `relIndex_saturation_eq_inf_ker_relIndex` and `map_relIndex_eq_saturation_relIndex`: the two factors expressed through the saturated subgroup `K ∩ (L ⊔ ker d)`.
- `relIndex_eq_map_relIndex_mul_inf_ker_relIndex`: `[K : L] = [d(K) : d(L)] · [K ∩ ker d : L ∩ ker d]` for `Subgroup.relIndex`, without finiteness assumptions.
- `intersectionIndexCardinal L K`: the cardinality of the coset type `K / (L ∩ K)`; `relativeIndexCardinal h` is the same for an inclusion `h : L ≤ K`.
- `relativeIndexCardinal_eq_index_of_finite`: when the coset type is finite, the cardinal index is the cast of `relIndex`.
- `relativeIndexCardinal_self` (index one) and `relativeIndexCardinal_mul`: multiplicativity in towers `M ≤ L ≤ K`.
- `intersectionIndexCardinal_image_eq_saturation`, `relativeIndexCardinal_kernel_eq_saturation` and `relativeIndexCardinal_eq_map_mul_inf_ker`: the cardinal image–kernel identity.

All identities come from explicit equivalences of coset types (a second-isomorphism argument at the level of sets), combined with the tower formula.

## Points to watch

- The natural-valued identity holds under Mathlib's convention that an infinite index is `0`; the cardinal version keeps infinite indices as infinite cardinals.
- In the cardinal identity `G` and `D` may live in different universes `u` and `v`, so both sides carry `Cardinal.lift`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Indices.lean`: the Lean file is the source byte for byte (SHA-256 `66b507525f34b853fa674a6695947c2d571230334424bf20ce7fa3d0f779a457`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
