# Completed projective tensor products of nonarchimedean normed algebras

`Langlands.Analysis.NonarchimedeanCompletedTensorStatement` is the proposition
that the following holds in every universe `u`.

Let `F` be a complete nontrivially normed field with ultrametric norm, and let
`E` and `E'` be normed commutative `F`-algebras whose norms are ultrametric
(no completeness of `E`, `E'` is assumed). Then there are a complete normed
commutative `F`-algebra `W` with ultrametric norm and an `F`-algebra map
`τ : E ⊗[F] E' → W` from the algebraic tensor product such that

- `τ` is injective, and
- `‖τ (e ⊗ e')‖ ≤ ‖e‖ * ‖e'‖` for all `e ∈ E`, `e' ∈ E'`.

## Provenance

L. Gruson and M. van der Put, "Banach spaces", Mém. Soc. Math. France 39–40
(1974), §5 (printed pp. 76–78): on `E ⊗ F` they define the projective seminorm
`‖a‖ = inf max ‖e_i‖ ‖f_i‖` over representations `a = Σ e_i ⊗ f_i`; Lemma 5.2(1)
gives the lower bound `‖Σ e_i ⊗ f_i‖ ≥ α max ‖e_i‖ ‖f_i‖` for `α`-orthogonal
families `e_i` (with T. A. Springer's alternative proof by `β`-orthogonal bases
of finite-dimensional subspaces), Lemma 5.2(2) concludes that this seminorm is
a norm with `‖e ⊗ f‖ = ‖e‖ ‖f‖`, and the completed tensor product is defined as
the completion for this norm.

The recorded statement is the consequence used here: for normed algebras the
projective seminorm is submultiplicative and ultrametric, so the completion `W`
of `E ⊗[F] E'` is a complete ultrametric normed `F`-algebra, and Lemma 5.2(2)
makes the canonical map into it injective. Only the inequality `≤` on pure
tensors is recorded; Gruson–van der Put state equality. The source treats
Banach spaces; the cited argument uses only completeness of `F` (through
finite-dimensional subspaces and their almost orthogonal bases), so the
statement does not require `E` or `E'` to be complete.
