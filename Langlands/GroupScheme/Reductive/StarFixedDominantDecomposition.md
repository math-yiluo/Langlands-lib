# Star-fixed weights as differences of dominant star-fixed weights

This module supplies the lattice step used to extend the Tits class from
dominant star-fixed weights to all star-fixed weights. Tits (*Représentations
linéaires irréductibles d'un groupe réductif sur un corps quelconque*,
J. reine angew. Math. 247 (1971), Corollary 3.5) extends the monoid
homomorphism on dominant star-fixed weights to the group of star-fixed
weights. That extension needs each star-fixed weight to be a difference of
two dominant star-fixed weights, which is proved here.

## Setting

- `d : GaloisPinningData k K G` is a Galois pinning. `P` is its root datum on
  the integral character lattice `X` of the torus, and `B` is its base.
- `hspan : P.corootSpan ℤ = ⊤` says the integral coroots span the cocharacter
  lattice. For simply connected `G` this is the published
  `corootSpan_eq_top_of_simplyConnected`. Under this hypothesis, the
  published `fundamentalWeightBasis P B hspan` is the integral basis
  `(ϖ_a)` of `X` dual to the simple coroots: `⟨ϖ_a, α_b^∨⟩ = δ_ab`.
- `d.IsStarFixedWeight λ` (published, `InnerStarWeights`) means
  `(starAction σ).weightEquiv λ = λ` for every `σ`.
- `IsDominantWeight λ` (published) means `⟨λ, α_a^∨⟩ ≥ 0` for every simple
  root `a`.

## Declarations

- `pairing_weightEquiv_coroot`: for a root-datum automorphism `e`,
  `⟨e x, α^∨_{e i}⟩ = ⟨x, α_i^∨⟩`. This is Mathlib's
  `RootPairing.Equiv.coroot'_weightEquiv`.
- `pairing_coroot_indexEquiv_of_fixed`: if `e λ = λ`, then
  `⟨λ, α^∨_{e i}⟩ = ⟨λ, α_i^∨⟩`.
- `isDominantWeight_add`: sums of dominant weights are dominant.
- `isStarFixedWeight_sub`: differences of star-fixed weights are star-fixed.
- `dominantPart hspan λ = ∑_a max(⟨λ, α_a^∨⟩, 0) ϖ_a`, the positive part of
  `λ` in the fundamental-weight basis. It is defined through the basis
  coordinate equivalence `equivFun`.
- `pairing_dominantPart`: `⟨dominantPart λ, α_a^∨⟩ = max(⟨λ, α_a^∨⟩, 0)` for
  each simple root `a`. Hence `dominantPart λ` and `dominantPart λ - λ` are
  dominant (`isDominantWeight_dominantPart`,
  `isDominantWeight_dominantPart_sub`). The second has pairings
  `max(⟨λ, α_a^∨⟩, 0) - ⟨λ, α_a^∨⟩ ≥ 0`.
- `isStarFixedWeight_dominantPart`: if `λ` is star-fixed, so is
  `dominantPart λ`. Let `e` be the star automorphism of `σ`. It is a based
  automorphism, so its index bijection permutes the simple roots. Compare
  coordinates in the fundamental-weight basis: write a simple root `i` as
  `e j` with `j` simple. Then
  `⟨e(dominantPart λ), α_{e j}^∨⟩ = max(⟨λ, α_j^∨⟩, 0)
    = max(⟨λ, α_{e j}^∨⟩, 0)`,
  where the last step uses star-fixedness of `λ`.
- `exists_dominant_sub`: every star-fixed `λ` is `a - b` with `a`, `b`
  dominant and star-fixed. Take `a = dominantPart λ` and
  `b = dominantPart λ - λ`.
