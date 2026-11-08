# The completion tensored with a finite separable extension

Formal proof: Worker 105. Verification and submission: Worker 1568.

This module proves `Langlands.AlgebraicGeometry.PointTopology.TensorCompletionProductStatement`:

```lean
theorem tensorCompletionProduct : TensorCompletionProductStatement.{u}
```

Let `K` be a nontrivially normed field, and let `v = NormedField.toAbsoluteValue K` be its norm as an absolute value, with completion `K_v = v.Completion`. Let `L/K` be finite separable. The statement asserts:

* only finitely many absolute values `w` on `L` lie over `v` (`w.LiesOver v`);
* `K_v ⊗_K L` is isomorphic, as a `K_v`-algebra, to `∏_w L_w`. Here `L_w = w.Completion` is a `K_v`-algebra through Mathlib's `AbsoluteValue.Completion.algebraOfLiesOver`.

This is the decomposition recalled on printed p.14 of Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011).

## Auxiliary results

All declarations are in the namespace `TensorCompletionProduct`.

* `completionNormedField K`: the nontrivially normed field structure on `K_v`.
* `norm_algebraMap` and `denseRange_algebraMap`: `K → K_v` preserves norms and has dense image.
* `coeL w`, `norm_coeL`, `denseRange_coeL`: the inclusion `L → L_w` as a `K`-algebra map. It satisfies `‖x‖ = w x`, and its image is dense.
* `norm_algebraMap_over`: the map `K_v → L_w` preserves norms (`UniformSpace.Completion.isometry_mapRingHom`).
* `exists_factor`: an algebra map from a finite product of fields to a field factors through one projection. Of the orthogonal idempotents `Pi.single i 1`, exactly one maps to `1`.
* `pullback u f`: the absolute value `x ↦ u (f x)`.

## Proof of `main`

1. `L` is étale over `K`, so `K_v ⊗_K L` is étale over `K_v`. Hence there is `e : K_v ⊗_K L ≅ ∏_{i ∈ I} E_i`, where `I` is finite and each `E_i` is a finite separable field extension of `K_v` (`Algebra.Etale.iff_exists_algEquiv_prod`).
2. Each `E_i` is algebraic over the complete field `K_v`. So it has a unique absolute value `a_i` extending the norm of `K_v` (`completeHenselianValuedField`). With `ι_i : L → E_i`, the absolute value `w_i = a_i ∘ ι_i` lies over `v`.
3. Every `w` over `v` is some `w_i` (`hfac`). The map `K_v ⊗_K L → L_w` composed with `e⁻¹` factors through some `E_i` via `μ : E_i → L_w` (`exists_factor`). The absolute value `‖μ(·)‖` extends the norm of `K_v`, so it equals `a_i`, and `w = w_i` on `L`.
4. `i ↦ w_i` is injective (`hinj`).
   * Suppose `w_i = w_k` with `i ≠ k`. The idempotent `ε = e⁻¹(Pi.single i 1)` maps to `1` in `E_i` and to `0` in `E_k`.
   * Expand `ε` in the basis `1 ⊗ b_m`, and approximate its coefficients by elements of `K`. This gives `y ∈ L` with `a_j(ι_j y - ε_j) ≤ δ · ∑_m w_j(b_m)` for every `j`, where `δ = 1 / (4(S + 1))` and `S = ∑_m w_i(b_m)`.
   * Then `1 ≤ w_i(y) + δS` and `w_k(y) ≤ δS`, while `w_i(y) = w_k(y)` and `2δS < 1`. This is a contradiction.
5. So `i ↦ w_i` is a bijection `I ≃ {w // w.LiesOver v}`, and the set of `w` is finite.
6. For each `i`, step 3 applied to `w_i` gives `μ : E_i → L_{w_i}`, injective because `E_i` is a field. Its image is a finite-dimensional `K_v`-subspace, which is closed (`Submodule.closed_of_finiteDimensional`, using `ContinuousSMul`). The image contains the dense image of `L`. So `μ` is an isomorphism.
7. Composing `e`, the factorwise isomorphisms (`AlgEquiv.piCongrRight`) and the reindexing along the bijection (`AlgEquiv.piCongrLeft`) gives `K_v ⊗_K L ≅ ∏_w L_w`.

## Source and scope

The source is registered as `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`, printed p.14,
the paragraph beginning with a finite separable extension of a valued field. The auxiliary
lemmas and estimates above are internal steps of this proof. The theorem has arbitrary universe
`u` and exactly the hypotheses of the published target. It proves only the tensor decomposition
assertion from the six-part statement module.
