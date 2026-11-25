# Continuity of the Galois action on the field of norms

Module `FontaineWintenberger.FieldOfNorms.Galois.Action`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` satisfy the library's class `IsPerfectResidueLocalField`, and let `L/K` be an infinite separable APF extension. The group `L ≃ₐ[K] L`, with its Krull topology, acts on `FieldOfNorms K L` through `FieldOfNorms.aut`. The file proves that every orbit map is continuous for the valuation topology of the field of norms. When `L` is a normal intermediate field of a separable closure `Ω` of `K`, it defines the action of the Galois group of `Ω/K` by restriction and determines its kernel and image. The file relates this to Wintenberger's Remark 3.2.4.

## Continuity

- `FieldOfNorms.coord_mapEquiv_of_mem_fixingSubgroup`: if `σ` fixes a finite intermediate field `E` pointwise, then `FieldOfNorms.mapEquiv σ` does not change the coordinate at `E` of any norm family. No normality is needed.
- `FieldOfNorms.valuation_sub_le_of_mem_deep_fixingSubgroup`: if `σ` fixes the `n`-th field of `deepFiniteTower K L` starting from the bottom field, then for every `x` of valuation at most `1`, the valuation of `σ x − x` is at most `exp(−(n + 2))`.
- `FieldOfNorms.continuous_aut_apply_of_integral`: for `x` of valuation at most `1`, the map `σ ↦ FieldOfNorms.aut K L σ x` is continuous.
- `FieldOfNorms.continuous_aut_apply`: the same for every `x`.

Proof: the truncation homomorphism `FieldOfNorms.truncation` at level `n`, from the valuation ring of the field of norms, depends only on the coordinate at the `n`-th deep field and has as kernel the elements of the stated precision (`truncation_eq_zero_iff`). Fixing subgroups of finite fields are open in the Krull topology, and `aut σ₀` preserves the valuation, which gives continuity at any `σ₀`. A general element is a quotient of two integral ones.

## The action of the Galois group of `Ω/K`

Here `Ω` is a separable closure of `K` and `L` an intermediate field, normal over `K`, APF and infinite.

- `FieldOfNorms.absoluteAut K L`: the homomorphism from `Ω ≃ₐ[K] Ω` to ring automorphisms of `FieldOfNorms K L`, the composite of `AlgEquiv.restrictNormalHom L` and `FieldOfNorms.aut K L`.
- `FieldOfNorms.coe_coord_absoluteAut`: the coordinate formula, read in `Ω`.
- `FieldOfNorms.absoluteAut_valuation`, `FieldOfNorms.continuous_absoluteAut_apply`: the action preserves the valuation, and orbit maps are continuous.
- `FieldOfNorms.absoluteAut_ker`: the kernel is `L.fixingSubgroup`; this uses `FieldOfNorms.aut_injective`.
- `FieldOfNorms.absoluteAut_range`: the image equals the image of `FieldOfNorms.aut K L`, since every automorphism of `L/K` extends to `Ω`.

## To watch for

- Continuity is proved for each orbit map `σ ↦ σ x`; joint continuity of the action is not stated.
- In the second part the Galois group of `Ω/K` acts on the field of norms of `L/K`, not on a separable closure of it; this part requires `L` normal over `K`.

## Reference

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3; Remark 3.2.4.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Galois/Action.lean` (SHA-256 of the source file `69552e0e2af0bb3e0a4c33456d034c87b219688e528de2e7ada525529b4d73fd`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
