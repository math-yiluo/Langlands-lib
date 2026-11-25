# The relative field of norms

Module `FontaineWintenberger.FieldOfNorms.Relative.Defs`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field with perfect residue field, `L/K` an infinite separable APF extension, and `M/L` a separable algebraic extension. Each finite subextension `N` of `M/L` is again infinite APF over `K`, so it has a norm field `FieldOfNorms K N`. The file defines `RelFieldOfNorms K L M`, the field of Wintenberger's paragraph 3.2.1, as the direct limit of these norm fields, gives it a valuation with rational values, and makes it functorial in `M`.

## Main definitions

* `RelFieldOfNorms.transition`: for `N ≤ P` in `FiniteIntermediateField L M`, the map `FieldOfNorms.inclusion K N P`; these form a directed system.
* `RelFieldOfNorms K L M`: Mathlib's `DirectLimit` of this system, a field. `RelFieldOfNorms.of N` is the map from the stage `N`; `RelFieldOfNorms.baseHom` is the map from `FieldOfNorms K L`, which makes the limit an algebra over the base norm field; `RelFieldOfNorms.ofAlgHom` is the stage map as an algebra homomorphism.
* `RelFieldOfNorms.stageExponent N`: the positive integer `e` with `v_N(x) = v_L(x)^e` for `x` in the base norm field, defined by choice and unique (`stageExponent_unique`).
* `RelFieldOfNorms.valueMap e`: the map of value groups `ℤ → ℚ`, `z ↦ z / e`, with zero adjoined. `RelFieldOfNorms.stageValuation N` is the valuation of `FieldOfNorms K N` divided by `stageExponent N`.
* `RelFieldOfNorms.valuation`: the valuation on the limit, with values in `WithZero (Multiplicative ℚ)`; a `Valued` instance is registered from it.
* `RelFieldOfNorms.mapEquiv t`, `RelFieldOfNorms.algMap t`: for an `L`-embedding `t : M → M'`, the induced map of limits, built from `RelFieldOfNorms.stageMap`. `RelFieldOfNorms.congr e` is the isomorphism induced by `e : M ≃ₐ[L] N`; `RelFieldOfNorms.uLiftEquiv` is the case of a universe lift.
* `RelFieldOfNorms.finiteEquiv`, `RelFieldOfNorms.finiteAlgEquiv`: for `M/L` finite, the isomorphism `RelFieldOfNorms K L M ≃ FieldOfNorms K M`.

## Main results

* `RelFieldOfNorms.of_injective`, `exists_stage`, `exists_finiteStage`, `exists_polynomial`: stage maps are injective, and every element, finite family or polynomial of the limit comes from one stage.
* `RelFieldOfNorms.isSeparable`: the limit is separable algebraic over `FieldOfNorms K L`.
* `RelFieldOfNorms.stageValuation_transition`: the normalized stage valuations are compatible with transitions. `RelFieldOfNorms.valuation_of` and `valuation_base` compute the limit valuation on a stage and on the base.
* `RelFieldOfNorms.map_base`, `map_valuation`, `map_injective`, `map_id`, `map_comp`: the induced maps fix the base norm field, preserve the valuation, are injective and functorial.
* `RelFieldOfNorms.finiteEquiv_of`, `finiteEquiv_valuation`: the finite comparison is `FieldOfNorms.inclusion` on each stage, and respects the valuations after rescaling.

## Remarks

* `RelFieldOfNorms.mapEquiv` is, despite its name, a ring homomorphism induced by an embedding, not an equivalence.
* The valuation is normalized on the base norm field, hence rational-valued.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3, paragraphs 3.2.1 and 3.2.6.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Relative/Defs.lean` (SHA-256 of the source file `0704f8b0b2aec14cd3d25b2a2fe67d7fc568337996a88b4cdd1ee9f076307ac0`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
