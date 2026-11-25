# The ambient Galois action on the relative field of norms

Module `FontaineWintenberger.FieldOfNorms.Galois.RelAction`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field with perfect residue field (`IsPerfectResidueLocalField K`), `Ω` a separable closure of `K`, and `L ⊆ Ω` an intermediate field that is normal over `K`, APF and of infinite degree. The relative field of norms `RelFieldOfNorms K L Ω` is the direct limit of the norm fields `FieldOfNorms K N` over the finite extensions `N` of `L` inside `Ω`. An automorphism `σ` of `Ω` over `K` carries each such `N` to `σ(N)`, again finite over `L`, and the induced isomorphisms of norm fields glue to an automorphism of the limit. This is the action of Wintenberger's Remark 3.2.4.

## Main definitions

* `RelFieldOfNorms.absoluteLayerField`, `RelFieldOfNorms.absoluteLayer`: for any field extension `M/K`, `L ⊆ M` normal over `K` and `N` a finite extension of `L` in `M`, the image `σ(N)` as an intermediate field of `M/L`, and as an element of `FiniteIntermediateField L M`. `RelFieldOfNorms.absoluteLayerEquiv` is the `K`-isomorphism `N ≃ σ(N)`. Lemmas say that `σ(N)` contains `L` and is finite over `L`, and that `N ↦ σ(N)` is monotone and compatible with `1` and with products.
* `RelFieldOfNorms.stageEquiv`: a `K`-isomorphism `N ≃ P` of finite stages gives the ring isomorphism `FieldOfNorms K N ≃ FieldOfNorms K P` (it is `FieldOfNorms.mapEquiv`). `stageEquiv_base` and `stageEquiv_transition` give its compatibility with the maps from `X_K(L)` and with the transition maps.
* `RelFieldOfNorms.absoluteStageMap`, `RelFieldOfNorms.absoluteMap`: the stage isomorphism attached to `σ`, and the ring endomorphism of the direct limit it induces.
* `RelFieldOfNorms.absoluteAut`: the group homomorphism from `Ω ≃ₐ[K] Ω` to the ring automorphisms of `RelFieldOfNorms K L Ω`.

## Main results

* `RelFieldOfNorms.absoluteAut_of`: on the image of a stage `N`, `σ` acts by `FieldOfNorms.mapEquiv` of `N ≃ σ(N)`, landing in the stage `σ(N)`.
* `RelFieldOfNorms.absoluteAut_base`: on the image of `X_K(L)` under `RelFieldOfNorms.baseHom`, the action is `FieldOfNorms.absoluteAut K L σ`, so it extends the action on the base norm field.
* `RelFieldOfNorms.absoluteAut_restrictScalars`: for `τ` an automorphism of `Ω` over `L`, the action of `τ` restricted to `K` is the functorial map `RelFieldOfNorms.mapEquiv` of `τ`.
* `RelFieldOfNorms.absoluteAut_valuation`: the action preserves `RelFieldOfNorms.valuation`.

## Proofs

Multiplicativity is checked stage by stage with `RelFieldOfNorms.of_transport_congr` and `FieldOfNorms.mapEquiv_trans`. For the valuation, `RelFieldOfNorms.stageEquiv_exponent` shows that `N` and `σ(N)` have the same normalization exponent, by the uniqueness statement `RelFieldOfNorms.stageExponent_unique`; then `RelFieldOfNorms.stageEquiv_valuation` gives equality of the stage valuations.

## Remarks

The action is constructed as a homomorphism into ring automorphisms; the file states no continuity of the action, only preservation of the valuation. The first section (images of finite layers) is pure field theory and needs only that `L/K` is normal.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3, Remark 3.2.4.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Galois/RelAction.lean` (SHA-256 of the source file `70f5a2dc5be2ea2f7329c0422f57ed59d1636c7d7a1c69a7e3367a73e9d690b8`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
