# A valued field is henselian exactly when it is separably closed in its completion

This module proves `Langlands.AlgebraicGeometry.PointTopology.HenselianIffSeparablyClosedStatement`:

```lean
theorem henselianIffSeparablyClosed : HenselianIffSeparablyClosedStatement.{u}
```

For every nontrivially normed field `K`, `IsHenselianValuedField K` holds if and only if `separableClosure K (UniformSpace.Completion K) = ⊥`. In words, the norm of `K` extends uniquely to every algebraic extension exactly when `K` is separably algebraically closed in its completion `K̂`. This is the characterization recalled on printed p.14 of Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011).

## Imports

The proof relies on three other modules:

* the published theorem `separableClosure_completion_eq_bot` (module `HenselianEtalePointProof`), which gives the forward direction;
* `completeHenselianValuedField` and `CompleteHenselian.absoluteValue_eq` (modules `CompleteHenselianValuedFieldProof` and `CompleteHenselianValuedField`): complete fields are henselian valued fields, and over a complete field, absolute values on an algebraic extension that extend the norm are unique;
* `HenselianTensorCompletion.irreducible_map` (module `HenselianTensorCompletionFieldProof`): if `K` is separably closed in `F`, a monic, irreducible, separable polynomial over `K` stays irreducible over `F`.

## Proof of the converse

Assume `separableClosure K K̂ = ⊥`. The module works in the namespace `HenselianIffSeparablyClosed` and uses two auxiliary definitions:

* `pullback u f` is the absolute value `x ↦ u (f x)` along a field map `f`.
* `completionNormedField K` is the nontrivially normed field structure on `K̂`, extending Mathlib's `NormedField` instance. Nontriviality comes from that of `K`, because the inclusion `K → K̂` preserves norms.

The proof has three steps.

* **Existence** (`exists_extension`). This step does not use the hypothesis. Let `L/K` be algebraic, and let `Ω` be an algebraic closure of `K̂`. There is a `K`-embedding `τ : L → Ω` (`IsAlgClosed.lift`). The complete field `K̂` is a henselian valued field, so its norm extends to an absolute value `u` on `Ω`. Then `pullback u τ` extends the norm of `K`.
* **Uniqueness for finite separable `L`** (`eq_of_finiteDimensional`).
  * Let `α` be a primitive element of `L`, with minimal polynomial `f`. By the hypothesis and `irreducible_map`, the image `f̂` of `f` over `K̂` is irreducible. So `E = AdjoinRoot f̂` is a field, finite over `K̂`. The power basis gives a `K`-algebra map `φ : L → E` sending `α` to the root.
  * Let `w` be an absolute value on `L` extending the norm of `K`, and let `L_w = w.Completion` be the completion of `L` at `w`. The map `K → L → L_w` is an isometry, so it extends to an isometric ring map `ι : K̂ → L_w` (`UniformSpace.Completion.mapRingHom`). The image of `α` in `L_w` is a root of `f̂` under `ι`, which gives `Ψ : E → L_w` (`AdjoinRoot.lift`). Viewed as maps of `K`-algebras, `Ψ ∘ φ` and the inclusion `L → L_w` agree on `α`. Hence they agree everywhere (`PowerBasis.algHom_ext`).
  * The absolute value `a_w = pullback ‖·‖ Ψ` on `E` therefore extends the norm of `K̂`, and `a_w ∘ φ = w`.
  * For two extensions `v` and `w`, uniqueness over the complete field `K̂` (`CompleteHenselian.absoluteValue_eq`) gives `a_v = a_w`. Composing with `φ` gives `v = w`.
* **Uniqueness for algebraic `L`** (`eq_of_isAlgebraic`). Let `y` be separable over `K`. Then `K⟮y⟯` is finite and separable over `K`, and the restrictions of `v` and `w` to it agree by the previous step, so `v y = w y`. For an arbitrary `x`, `L` is purely inseparable over the separable closure of `K` in `L`. So some power `x ^ (q ^ n)`, where `q` is the exponential characteristic, is separable over `K` (`IsPurelyInseparable.pow_mem`). Then `v x ^ (q ^ n) = w x ^ (q ^ n)`, and `v x = w x` because both are nonnegative.

`isHenselianValuedField_of_separableClosure_eq_bot` combines existence and uniqueness. The entry theorem pairs this converse with `separableClosure_completion_eq_bot`.
