# Archimedean henselian fields

Author: Worker 105. Checked and prepared for submission by Worker 362.

This module proves `Langlands.AlgebraicGeometry.PointTopology.ArchimedeanHenselianStatement`:

```lean
theorem archimedeanHenselian : ArchimedeanHenselianStatement.{u}
```

The statement concerns a nontrivially normed field `K` that is not non-archimedean (`¬ IsUltrametricDist K`). It says that `IsHenselianValuedField K` holds if and only if the following holds. There is a ring map `σ : K → ℂ` and a real `s` with `0 < s ≤ 1` and `‖x‖ = ‖σ x‖ ^ s` for all `x`, and either `K` is algebraically closed, or `σ` is real-valued and `K` is real closed (Mathlib's `IsRealClosed`). This is Conrad's description, on printed p.14 of *Weil and Grothendieck approaches to adelic points* (December 31, 2011), of the archimedean henselian fields as the algebraically closed subfields of `ℂ` and the real closed subfields of `ℝ`, with the induced absolute value up to a power.

## Imports

The proof uses these modules:

* `HenselianIffSeparablyClosedProof`: the criterion `isHenselianValuedField_of_separableClosure_eq_bot`, and the nontrivially normed structure `completionNormedField K` on the completion `K̂`;
* the published theorem `separableClosure_completion_eq_bot`: a henselian field is separably closed in `K̂`;
* `CompleteHenselianValuedFieldProof`:
  * `exists_rpow_of_not_ultrametric`: an archimedean field has characteristic `0`, and its norm on `ℚ` is `|·|^s`;
  * `exists_complex_rpow`: a complete archimedean field has a map `φ` to `ℂ` with `‖y‖ = ‖φ y‖^s`;
  * `realHom` and `continuous_realHom`: the continuous extension `ψ : ℝ → K̂` of `ℚ → K̂`;
* `Langlands.FieldTheory.RealClosedIrreducibleDegree`: irreducible polynomials over a real closed field with a map to `ℝ` have degree at most `2`.

## Auxiliary results

The namespace `HenselianArchimedean` contains these auxiliary results:

* `real_exists_isRoot_of_odd`: a real polynomial of odd degree has a real root. The proof applies the intermediate value theorem between `-∞` and `+∞`, using `f(-X)` for the limit at `-∞`.
* `uniformContinuous_of_rpow`: a map with `‖x‖ = ‖σ x‖^s` is uniformly continuous.
* `realPart σ`: the ring map `x ↦ re (σ x)` when `σ` is real-valued.
* `mem_range_of_aeval_eq_zero` and `exists_root_of_aeval_eq_zero`: suppose `K` has characteristic `0` and is separably closed in `K̂`. Then a root in `K̂` of a nonzero polynomial over `K` lies in `K`.

## Proof

**Backward direction.**

* `separableClosure_eq_bot_of_isAlgClosed`: if `K` is algebraically closed, the minimal polynomial of every algebraic element of `K̂` has degree `1`.
* `separableClosure_eq_bot_of_isRealClosed`: suppose `K` is real closed and `σ` is real.
  * `σ` extends to a continuous ring map `σ' : K̂ → ℂ` (`UniformSpace.Completion.extensionHom`), which is real-valued by density.
  * Let `x ∈ K̂` be separable over `K`. Its minimal polynomial has degree at most `2` (`natDegree_le_two_of_irreducible` with `τ = realPart σ`).
  * Suppose the degree is `2`, with `x² + bx + c = 0`. The discriminant `δ = b² - 4c` is not a square in `K`, so `-δ = e²` with `e ≠ 0`. Then `σ'(2x + b)² = -σ(e)²` with both sides real, which forces `σ e = 0`, a contradiction.

In both cases `isHenselianValuedField_of_separableClosure_eq_bot` concludes.

**Forward direction** (`exists_of_isHenselianValuedField`).

* `K̂` is not non-archimedean, since the norms of the naturals agree. So `exists_rpow_of_not_ultrametric` and `exists_complex_rpow` give `s` and `φ : K̂ → ℂ`. Put `σ = φ ∘ (K → K̂)`.
* `φ` is continuous. So `φ ∘ ψ` agrees with the inclusion `ℝ → ℂ` on `ℚ`, hence everywhere (`DenseRange.equalizer`).
* `K` is separably closed in `K̂` and has characteristic `0`.
* If `σ` is real, then `ψ (re σ x) = x` in `K̂`. The three conditions for `IsRealClosed K` follow:
  * a sum of squares has nonnegative image in `ℝ`, so `-1` is not one;
  * for `x` or `-x`, the image of a real square root under `ψ` is a root of `X² ∓ x` in `K̂`, hence lies in `K`;
  * an odd-degree `f` has a real root `t` of `f^τ`, and `ψ t` is a root of `f` in `K̂`, hence `f` has a root in `K`.
* If `σ x₀` is not real for some `x₀`, then every `w ∈ ℂ` is `φ (ψ a + ψ b · x₀)` for suitable real `a` and `b`. So a root in `ℂ` of `p^σ` gives a root of `p` in `K̂`, hence in `K`. By `IsAlgClosed.of_exists_root`, `K` is algebraically closed.

## Source

Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011), printed p.14, the paragraph immediately before Lemma 5.3. Registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. The classification is the source assertion; the completion-embedding proof above is the implemented derivation.
