# For henselian `K`, the completion tensored with a finite separable extension is a field

This module proves `Langlands.AlgebraicGeometry.PointTopology.HenselianTensorCompletionFieldStatement`:

```lean
theorem henselianTensorCompletionField : HenselianTensorCompletionFieldStatement.{u}
```

The statement says the following. Let `K` be a nontrivially normed field that is a henselian valued field, and let `L` be a finite separable extension of `K`. Then `K̂ ⊗_K L` is a field, and its dimension over `K̂ = UniformSpace.Completion K` is `[L : K]`. This is part of the remark on printed p.14 of Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011): for henselian `k`, `k̂ ⊗_k k'` is a field for every finite separable extension `k'/k`.

## Proof

The dimension claim is `Module.finrank_baseChange`. The field claim uses one property of henselian fields: `K` is separably algebraically closed in `K̂`. This is the published theorem `separableClosure_completion_eq_bot` from `HenselianEtalePointProof`. The rest is field theory over any field extension `F/K` with `separableClosure K F = ⊥`. That part lives in the namespace `HenselianTensorCompletion`.

* `mem_lifts_of_dvd`: let `f` be a separable polynomial over `K`, and let `g` be a monic factor over `F` of the image of `f`. Then the coefficients of `g` lie in `K`. Pass to `Ω = AlgebraicClosure F`, where `g` splits as `∏ (X - β)`. Each root `β` is a root of `f`, so it is separable over `K` and lies in `separableClosure K Ω`. The product therefore has coefficients in `separableClosure K Ω`. The `K`-embedding `F → Ω` identifies `separableClosure K F` with the preimage of `separableClosure K Ω` (`map_mem_separableClosure_iff`). So each coefficient of `g` lies in `separableClosure K F = ⊥`, which is `K`.
* `irreducible_map`: a monic, irreducible, separable `f` over `K` stays irreducible over `F`. Take a factorization `f = g h` over `F` into monic factors. By the previous lemma, both factors lift to monic polynomials over `K` of the same degrees (`lifts_and_natDegree_eq_and_monic`). Since `K[X] → F[X]` is injective, their product is `f`. By irreducibility of `f`, one factor is a unit, so it has degree `0`.
* `isField_tensor`: `F ⊗_K L` is a field. Let `α` be a primitive element of `L` (`Field.powerBasisOfFiniteOfSeparable`) with minimal polynomial `f`, and let `E = AdjoinRoot (f.map (algebraMap K F))`. `E` is a field because the image of `f` is irreducible. The power basis gives a `K`-algebra map `L → E` sending `α` to the root. With `F → E`, it induces an `F`-algebra map `Φ : F ⊗_K L → E`. `Φ` is surjective because `1 ⊗ α` maps to the root, and the root generates `E`. Both sides have dimension `deg f = [L : K]` over `F`. So `Φ` is injective and hence an isomorphism, and `F ⊗_K L` is a field.

The entry theorem applies `isField_tensor` with `F = K̂`.
