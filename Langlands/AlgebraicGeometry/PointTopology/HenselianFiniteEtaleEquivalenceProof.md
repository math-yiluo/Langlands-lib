# Finite étale algebras over a henselian field and over its completion

This module proves `Langlands.AlgebraicGeometry.PointTopology.HenselianFiniteEtaleEquivalenceStatement`:

```lean
theorem henselianFiniteEtaleEquivalence : HenselianFiniteEtaleEquivalenceStatement.{u}
```

Let `K` be a henselian valued field with completion `K̂`. The statement has two parts:

1. For finite étale `K`-algebras `A` and `B`, the map `φ ↦ Algebra.TensorProduct.map (AlgHom.id K̂ K̂) φ`, from `K`-algebra maps `A → B` to `K̂`-algebra maps `K̂ ⊗_K A → K̂ ⊗_K B`, is bijective.
2. Every finite étale `K̂`-algebra `E` is isomorphic to `K̂ ⊗_K A` for some finite étale `K`-algebra `A`.

This is the equivalence between finite étale algebras over `k` and over `k̂` asserted on printed p.14 of Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011).

## Proof

`K` is separably closed in `K̂` (`separableClosure_completion_eq_bot`). Part 1 is `HenselianFiniteEtale.bijective_map`. Part 2 reduces to finite separable field extensions of `K̂` (`HenselianFiniteEtale.exists_etale_of_field`). The field case splits in two:

* Non-archimedean `K`: `HenselianFiniteEtale.exists_field_of_isUltrametricDist`, via Krasner's lemma.
* Archimedean `K`: `HenselianFiniteEtale.exists_field_of_not_isUltrametricDist`, proved here.
  * `K̂` carries the norm `HenselianIffSeparablyClosed.completionNormedField K`, and it is archimedean too, since the naturals have the same norms in `K` and in `K̂`.
  * As in `HenselianArchimedeanProof`, the completion has a ring map `φ : K̂ → ℂ` with `‖y‖ = ‖φ y‖^s` (`CompleteHenselian.exists_complex_rpow`). Let `ψ : ℝ → K̂` be the continuous extension of `ℚ → K̂` (`CompleteHenselian.realHom`). Both maps are continuous, so `φ (ψ r) = r` for every real `r`, by density of `ℚ` in `ℝ`.
  * If `φ` is real-valued, `K̂` is real closed. Square roots and roots of odd-degree polynomials are carried from `ℝ` by `ψ`. By `natDegree_le_two_of_irreducible`, a finite separable `E/K̂` has degree `1` or `2`.
    * In degree `1`, take `L = K`.
    * In degree `2`, `E` contains `ι` with `ι² = -1` (`exists_sq_eq_neg_one`). `ι` is not in `K`, since `φ` is real on `K`, so `L = K(ι)` has degree `2`.
  * Otherwise `φ` is onto `ℂ`. Then `K̂` is algebraically closed, since roots in `ℂ` pull back, so `E = K̂` and `L = K`.
  * In each case `HenselianFiniteEtale.nonempty_algEquiv_of_algHom` gives `K̂ ⊗_K L ≅ E`.
