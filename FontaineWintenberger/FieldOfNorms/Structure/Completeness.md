# Completeness of the field of norms

Module `FontaineWintenberger.FieldOfNorms.Structure.Completeness`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

For an infinite APF extension `L/K` of a field `K` with `IsPerfectResidueLocalField K`, the file proves that the field of norms `FieldOfNorms K L` is complete for its valuation. The valuation ring is compared, as a uniform space, with the inverse limit `deepNormInverseLimit K L D` of the truncated quotients `DeepFiniteTowerQuotient K L D n`, each with the discrete uniformity; `D` is any finite intermediate field.

## Main results

- `Valued.nhds_zero_hasBasis_integer_closedBall`: in a field valued in `WithZero (Multiplicative ℤ)` that has an element of valuation `exp(−1)`, the sets `{x | v x ≤ exp(−(n+2))}`, `n : ℕ`, form a basis of neighbourhoods of `0`.
- `FieldOfNorms.integral_nhds_zero_hasBasis`: the same basis for the valuation ring of the field of norms, with its subspace topology.
- `FieldOfNorms.truncationHom_comap_nhds_zero`: the truncation homomorphism into the inverse limit pulls the neighbourhoods of `0` back to the neighbourhoods of `0` of the valuation ring.
- `FieldOfNorms.truncationHom_isUniformInducing`: the truncation homomorphism is uniform inducing.
- `FieldOfNorms.integral_completeSpace`: the valuation ring is complete.
- `FieldOfNorms.instCompleteSpace` (an instance; the file calls it Theorem 2.1.3 (ii)): the field of norms is complete.
- `FieldOfNorms.t2Space`, `FieldOfNorms.integral_t2Space`: the field and its valuation ring are Hausdorff.

## Proofs

The kernel of the `n`-th projection of the inverse limit corresponds, by `FieldOfNorms.truncation_eq_zero_iff`, to the ball of radius `exp(−(n+2))`, so the two bases of neighbourhoods agree. The inverse limit of discrete spaces is complete, and the truncation map is surjective (`FieldOfNorms.truncationEquiv`), which gives completeness of the valuation ring. Completeness of the field follows from that of its valuation ring; the instance takes `D` to be the bottom field `K`. The existence of an element of valuation `exp(−1)` comes from `FieldOfNorms.uniformizer`.

## Points to watch

- The basis is indexed with a shift: the `n`-th set has radius `exp(−(n+2))`, matching the indexing of the truncations.
- The discrete uniformities on the quotients are introduced by `letI` inside the statements, not as global instances.
- Infinitude of `L/K` is the hypothesis `Fact (¬ Module.Finite K L)`.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Structure/Completeness.lean` (SHA-256 of the source file `41a818579975284b869acf269fd0d305d57b5a1011661e4647206e0e0f1939e2`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
