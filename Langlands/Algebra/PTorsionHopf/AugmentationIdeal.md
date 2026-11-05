# The augmentation ideal of the convolution dual and conilpotence

Author: Worker 1519, as internal infrastructure for the proof of
`Langlands.GroupScheme.RelativeRoot.SmoothCommutativePTorsionVectorStatement`.

Provenance: internal. The coradical-filtration language is standard coalgebra theory; the
statements and proofs below are the author's own implementation for the Mathlib convolution
ring, and no source statement is translated.

Notation: `k` is a field, `A` a commutative `k`-bialgebra, and the convolution dual is
`WithConv (A →ₗ[k] k)` (see `Verschiebung.md`).

## A generic nilpotence lemma

`exists_pow_le_of_finite_quotient K I hI`: in a commutative `k`-algebra `R`, let `K` be an
ideal with `R ⧸ K` finite-dimensional over `k`, and `I` an ideal each of whose elements has a
power in `K`. Then `I ^ N ≤ K` for some `N`. The quotient is a Noetherian ring, the image of
`I` is finitely generated and contained in the nilradical, hence nilpotent
(`Ideal.FG.isNilpotent_iff_le_nilradical`). The lemma is stated for an arbitrary ring `R`
because the same elaboration directly on the convolution dual is very slow.

## The augmentation ideal

- `evalOne : WithConv (A →ₗ[k] k) →+* k` is `ξ ↦ ξ 1`; multiplicativity uses
  `comul 1 = 1 ⊗ 1`.
- `augIdeal` is its kernel: the functionals vanishing at `1`. `mem_augIdeal` unfolds
  membership.
- `convMul_apply_eq_rightAct θ η b`: `(θ * η) b = θ (rightAct η b)`, where `rightAct` is the
  Library's right translation `b ↦ ∑ η(b₂) b₁`
  (`Langlands.GroupScheme.AffineLinearEmbedding.rightAct`).

## Annihilators of stable subspaces (cocommutative case)

Assume `Coalgebra.IsCocomm k A`, so the convolution dual is commutative.

- `annIdeal W hW`: for a subspace `W` stable under every right translation, the functionals
  vanishing on `W` form an ideal of the convolution dual (by `convMul_apply_eq_rightAct`).
  `mem_annIdeal` unfolds membership.
- `restrictDual W`: restriction of functionals to `W`, a `k`-linear map to
  `Module.Dual k W`, with `restrictDual_apply`.
- `finite_quotient_annIdeal W hW`: if `W` is finite-dimensional, the quotient of the dual by
  `annIdeal W hW` is finite-dimensional: it injects into `Module.Dual k W`.

## Conilpotence

`exists_pow_augIdeal_apply_eq_zero p hV a`: if every element of `augIdeal` has vanishing
`p`-th convolution power (`hV`), then for every `a : A` there is `N` with `θ a = 0` for all
`θ ∈ augIdeal ^ N`.

Proof as implemented: `W` is the Library's finite-dimensional right-translation stable span
`GroupScheme.Chevalley.regularSpan {a, 1}`; the generic lemma applied to `K = annIdeal W` and
`I = augIdeal` gives `augIdeal ^ N ≤ annIdeal W`, and `a ∈ W`.

Here `p` is only an exponent; no primality or characteristic hypothesis is used in this
module.
