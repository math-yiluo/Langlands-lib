# Irreducible polynomials over a real closed subfield of `ℝ` have degree at most two

Author: Worker 105. Checked and prepared for submission by Worker 362.

This module proves Artin's algebraic form of the fundamental theorem of algebra, for the real closed fields that occur in the archimedean henselian classification:

```lean
theorem Langlands.FieldTheory.RealClosedDegree.natDegree_le_two_of_irreducible
    {R : Type u} [Field R] [IsRealClosed R] (τ : R →+* ℝ) {g : R[X]} (hg : Irreducible g) :
    g.natDegree ≤ 2
```

Here `IsRealClosed R` is Mathlib's definition:

* `R` is semireal (`-1` is not a sum of squares);
* for every `x`, either `x` or `-x` is a square;
* every polynomial of odd degree has a root.

The ring map `τ : R → ℝ` is an extra hypothesis. It is used only to order `R`: an element of `R` is a square exactly when its image under `τ` is nonnegative. Mathlib's `IsRealClosed` does not supply an ordering, and this hypothesis provides one. It is satisfied in the application, where `R` embeds in `ℝ`. The statement is classical (E. Artin). The proof below is the standard Galois-theoretic one.

## Proof

All lemmas are in the namespace `Langlands.FieldTheory.RealClosedDegree`.

* `isSquare_of_nonneg` and `exists_sq_eq_of_nonneg`: an element `x` with `0 ≤ τ x` is a square. Moreover it has a square root `r` with `0 ≤ τ r`.
* `finrank_eq_one_of_odd`: an extension of `R` of odd degree is trivial. Since `R` has characteristic `0`, the extension has a primitive element. Its minimal polynomial is irreducible of odd degree, so it has a root and degree `1`.
* `exists_quadratic`: in an extension `L/E` of degree `2`, any element `α ∉ E` satisfies `α² + bα + c = 0` with `b, c ∈ E`. Its minimal polynomial has degree `2`.
* `false_of_forall_isSquare`: suppose `2 ≠ 0` in `E` and every element of `E` is a square. Then `E` has no extension of degree `2`. Write `b² - 4c = w²`. Then `(2α + b - w)(2α + b + w) = 0`, which puts `α` in `E`.
* `exists_sq_eq_neg_one`: a degree-`2` extension `F` of `R` contains `ι` with `ι² = -1`. With `α` as above, `γ = 2α + b` satisfies `γ² = δ := b² - 4c`. Here `δ` is not a square in `R`, since otherwise `α ∈ R`. So `-δ = e²` with `e ≠ 0`, and `ι = γ / e` works.
* `forall_isSquare_of_finrank_eq_two`: every element of a degree-`2` extension `F` of `R` is a square.
  * `ι ∉ R`, because `τ(t)² = -1` is impossible. So `1, ι` is a basis of `F`, and every element of `F` is `a + bι`.
  * Let `r` be a square root of `a² + b²` with `τ r ≥ 0`. Then `τ r ≥ |τ a|`. So `(r + a)/2 = c²` and `(r - a)/2 = d²` for some `c, d`, and the sign of `d` can be chosen so that `2cd = b`, because `(2cd)² = r² - a² = b²`.
  * Then `(c + dι)² = a + bι`.
* `natDegree_le_two_of_irreducible`: let `SF` be the splitting field of `g`, which is Galois over `R` because `g` is separable in characteristic `0`.
  * The fixed field of a Sylow `2`-subgroup `P` of `Gal(SF/R)` has degree `[G : P]` over `R`, which is odd. So it is `R`, and `[SF : R] = 2^k`.
  * Suppose `k ≥ 2`. Take subgroups `H' ≤ H` of orders `2^(k-2)` and `2^(k-1)` (`Sylow.exists_subgroup_card_pow_prime` and `Sylow.exists_subgroup_card_pow_succ`). Then `F = SF^H` has degree `2` over `R`, and `SF^{H'}` has degree `2` over `F` (via `IntermediateField.extendScalars`). Every element of `F` is a square, so this contradicts `false_of_forall_isSquare`.
  * Hence `[SF : R] ≤ 2`. A root `θ` of `g` in `SF` has minimal polynomial `g / lc(g)`, of degree at most `[SF : R]`.

## Provenance

This is an internal prerequisite for the archimedean henselian classification. The full Galois-theoretic argument is implemented in Lean from the imported Mathlib definitions and theorems; the reference to Artin identifies the classical argument, rather than an additional assumed result.
