# A normalized ultrametric seminorm on the tensor product of two valued fields

`Langlands.Analytic.TensorSeminormStatement` asserts the following. Let
`E`, `F` and `G` be complete normed fields in one universe `Type u` whose
norms satisfy the strong triangle inequality (`IsUltrametricDist`). Let `F`
and `G` be normed `E`-algebras. Then the algebraic tensor product
`F ⊗[E] G` carries a ring seminorm `p` (Mathlib's `RingSeminorm`) such that

- `p 1 = 1`;
- `p` is nonarchimedean: `p (s + t) ≤ max (p s) (p t)` (`IsNonarchimedean p`);
- `p (a ⊗ₜ 1) ≤ ‖a‖` for every `a : F`;
- `p (1 ⊗ₜ b) ≤ ‖b‖` for every `b : G`.

A Mathlib `RingSeminorm` is nonnegative, vanishes at `0`, and satisfies
`p (s + t) ≤ p s + p t`, `p (-t) = p t` and `p (s * t) ≤ p s * p t`. The
proposition only asserts that such a `p` exists. It does not say that `p` is
multiplicative or separated, and it says nothing about a completed tensor
product.

Since `F` and `G` are normed algebras over the field `E` and `‖1‖ = 1` in a
normed field, the structure maps `E → F` and `E → G` preserve norms. So `F`
and `G` are valued-field extensions of `E`, with real-valued norms. Trivial
norms are allowed. All universes are allowed, including `u = 0`.

## Literature and provenance

This is an internal auxiliary interface for the common-field realization of
compatible affinoid points (task `4231d77c-8e1e-4ef5-9536-8a4f5c7fb60d`),
proposed by Worker 125. The intended witness is the tensor-product seminorm of
Ben Yaacov, *Tensor products of valued fields* (Bull. London Math. Soc. 47
(2015)), source `ben-yaacov-2015-tensor-products-valued-fields`, printed
page 2. Definition 6 sets
`‖z‖ = inf_{z = x̄ᵗ ⊗ ȳ} max_i ‖x_i‖ ‖y_i‖` on `U ⊗_k V`, for standard
semi-normed vector spaces `U` and `V` over a standard valued field `k`. In
that paper, semi-norms satisfy `‖x + y‖ ≤ max (‖x‖, ‖y‖)` and
`‖a x‖ = |a| ‖x‖`. Lemma 7(i) says this is a semi-norm, sub-multiplicative
for algebras with sub-multiplicative semi-norms. Lemma 7(iii) says
`‖x ⊗ y‖ = ‖x‖ ‖y‖`. With `x = a`, `y = 1` (and symmetrically), and with
`x = y = 1`, Lemma 7(iii) gives all three norm conditions of the proposition
with equality. The ring axioms, `p (-t) = p t` and the ordinary triangle
inequality are part of Mathlib's `RingSeminorm`. They follow from Lemma 7(i)
together with the strong triangle inequality.

The proposition is weaker than Lemma 7. It keeps only existence and the
inequalities that the downstream amalgamation argument uses. The
completeness hypotheses on `E`, `F` and `G` and the strong triangle inequality
on `E` reflect the setting of that argument. They are not needed for the
construction. The downstream argument chooses a normalized nonarchimedean
multiplicative seminorm `q` on `F ⊗[E] G` with `q t ≤ p t` for every `t`,
that is, `q` is dominated by `p`. It then realizes `q` in a complete field. For
nonzero `a : F`, the bounds give `q (a ⊗ₜ 1) ≤ ‖a‖` and
`q (a⁻¹ ⊗ₜ 1) ≤ ‖a‖⁻¹`, so multiplicativity and `q 1 = 1` force
`q (a ⊗ₜ 1) = ‖a‖`, and similarly on `G`. This yields a common complete valued
field containing isometric copies of `F` and `G` over `E`. The opposite
comparison `p ≤ q` is not available in general. This file states the
interface only; it proves nothing.
