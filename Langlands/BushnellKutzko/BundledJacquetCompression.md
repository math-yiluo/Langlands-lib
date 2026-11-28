# Nonvanishing Jacquet modules from injective compression

The module `Langlands.BushnellKutzko.BundledJacquetCompression` (namespace `Langlands.Jacquet`)
gives an abstract criterion for a nonzero Jacquet module, in the form used for the second proof
of BK93 (6.2.1): the remark after (7.3.2), printed p. 223, of C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), `bushnell-kutzko-1993-admissible-dual-gln` (PDF page = printed
page + 12).

The underlying `compressionMap` and its multiplication and normalization formulas are in [TypeJacquetCompression](TypeJacquetCompression.md).

## Contents

- `IsCompressionContraction K N M Nbar g`: for an open subgroup `K` of a topological group `G`,
  subgroups `N`, `M`, `Nbar` and `g ∈ M`, every `k ∈ K` factors as `l * m * u` with
  `l ∈ K ∩ Nbar`, `m ∈ K ∩ M`, `u ∈ K ∩ N`; conjugation by `g` maps `K ∩ N` into itself,
  conjugation by `g⁻¹` maps `K ∩ M` and `K ∩ Nbar` into themselves; and every element of `N`
  is carried into `K` by conjugation with some power of `g`. These are the clauses of the
  Library predicate `IsIwahoriContraction` without its uniform contraction of `K ∩ Nbar`;
  `IsCompressionContraction.ofIwahoriContraction` shows that the latter implies the former.
  The predicate is stronger than the Library's `Langlands.Jacquet.IsWeakIwahoriContraction`
  (module `Langlands.Representation.Jacquet.WeakIwahoriBasis`), which has only the Levi
  membership and the three conjugation conditions, not the factorization or the exhaustion.
- `compressionMap ρ hρ K hK g`: for a smooth representation `ρ` (`hρ`) and an open subgroup `K`
  that is compact (`hK`), the linear map `v ↦ e_K (ρ(g) v)`, where `e_K` is the normalized
  average over `K` (`Compact.averageMap`).
- `compressionMap_mul_of_factor`: on `K`-fixed vectors, compression by `x` after compression by
  `y` is compression by `x y`, when every element of `K` factors as `u * l` with
  `x u x⁻¹ ∈ K` and `y⁻¹ l y ∈ K`; `compressionMap_of_normalizes`: compression by an element `x`
  with `x⁻¹ K x ⊆ K` is its action on `K`-fixed vectors.
- `IsCompressionContraction.compressionMap_pow`: if `IsCompressionContraction K N M Nbar g`
  holds, then on `K`-fixed vectors the `r`-th power of compression by `g` is compression by
  `g^r`.
- `exists_pow_compressionMap_eq_zero_of_compressionContraction`: let `ρ` be smooth, `K` compact open,
  `IsCompressionContraction K N M Nbar g` hold and `M` normalize `N`. If the coinvariants
  `Jacquet.Coinvariants ρ N` vanish, every `K`-fixed vector is killed by some power of
  compression by `g`. The exhaustion clause of the contraction is essential: it puts the
  conjugates of each element of `N` by large powers of `g` into `K`.
- `not_subsingleton_coinvariants_of_compressionContraction`: let `K` be compact,
  `IsCompressionContraction K N M Nbar g` hold and `M` normalize `N`. Let `P` be a property of
  linear maps from a finite-dimensional space `W` into the `K`-fixed vectors, stable under
  composition with compression by `g`, and such that this composition is zero only for the
  zero map. If a nonzero map has `P`, then `Jacquet.Coinvariants ρ N` is not a subsingleton.

## Proofs

A vector in the span of the relations `ρ(n) w - w` with `n ∈ N` is killed by `e_K ∘ ρ(g^s)` for
all large `s`, because `g^s n g^(-s) ∈ K` for large `s`. Iterating the multiplicativity of
compression on `K`-fixed vectors gives the power formula. In the final theorem, a basis of `W`
yields a common power `R` killing the images of the given map `f`; then the `R`-fold composition
of compression with `f` is zero, and the injectivity hypothesis applied `R` times gives `f = 0`.
No admissibility of `ρ` is used.
