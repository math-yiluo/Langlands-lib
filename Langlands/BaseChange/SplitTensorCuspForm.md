# Split tensor products of test functions and cusp forms

`Langlands.BaseChange.splitTensorCuspForm` proves
`Langlands.BaseChange.SplitTensorCuspFormStatement.{u}`.
The theorem uses the published `splitTensor` and `HasVanishingConstantTerms` for
every nonarchimedean local field in universe `u` and every pair `n l : ℕ`.

## Test-function property

The proof uses `Global.RankinSelbergGlobal.UnipotentClass.glPiEquiv` to identify
`GL_n(F^l)` with `∏ᵢ GL_n(F)` as topological groups. Its coordinate maps are
exactly those used by `splitTensor`. For each `g`, the pullback of each
`φ i` to `GL_n(F^l)` is eventually equal to its value at `g` in the
neighborhood filter at `g`. Finiteness of `Fin l` makes these equalities hold
simultaneously on a neighborhood, so their product is locally constant.

Where the product is nonzero, every coordinate lies in the support of its
factor. The inverse image of the product of the factor topological supports
under `glPiEquiv` is closed and compact. It therefore contains the closure
of the support, which is compact as well. This argument includes the empty
product, whose domain `GL_n(F^0)` is a singleton.

## Vanishing constant terms

Fix a block shape `B` with at least two blocks, and write `U(R)` for
`B.unipotentSubgroup R`. The zero conditions below the diagonal blocks and the
identity conditions within them hold over `F^l` exactly when they hold in
every coordinate. They give a restriction of `glPiEquiv` to a topological
group isomorphism `U(F^l) ≃ₜ* ∏ᵢ U(F)`.

For every `x, y ∈ GL_n(F^l)`, the map `v ↦ x * v * y` on `U(F^l)` is the
closed subgroup inclusion followed by two translations, so it is a closed
embedding. Pulling back the test function along this map gives a continuous
compactly supported function. It is integrable against any Haar measure `μ`
on `U(F^l)`.

For the integral, push `μ` forward along the restricted isomorphism. Choose
one Haar measure `ν` on `U(F)` and use its finite product on `∏ᵢ U(F)`.
The local compactness and second countability of the groups give
sigma-finiteness and allow Haar uniqueness, so the pushforward is a scalar
multiple of that product measure. Multiplicativity of `glPiEquiv` identifies
the translated tensor in product coordinates with
`w ↦ ∏ i, φ i (xᵢ * w i * yᵢ)`. Mathlib's `integral_fintype_prod_eq_prod`
expresses the resulting integral as the Haar scalar times the product of the
coordinate integrals. If `φ i₀` satisfies `HasVanishingConstantTerms`, its
integral for `B`, `ν`, `xᵢ₀` and `yᵢ₀` is zero, so the whole product is zero.

## Provenance

This is the argument in the paired statement's “Why it holds” section,
formalized for the Library's two-sided constant-term predicate.
Arthur and Clozel use the split tensor functions in *Simple Algebras, Base
Change, and the Advanced Theory of the Trace Formula* (1989), Chapter 1,
§5, pp. 48–49 (`arthur-clozel-1989-base-change`). Henniart and Lemaire give
the trace-formula conditions on a cuspidal factor in *Changement de base
et induction automorphe pour GLₙ en caractéristique non nulle* (2011),
§II.6.3–4, pp. 120–121
(`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`).
