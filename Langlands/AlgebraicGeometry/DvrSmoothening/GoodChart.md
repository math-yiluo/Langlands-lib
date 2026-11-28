# Closures of points of ramification index one have good charts

`goodChartStatement` proves the Library proposition
`Langlands.AlgebraicGeometry.DvrSmoothening.GoodChartStatement`.

- `isLocalization_away_quotient`: localization away from an element commutes with quotients.
- `residueTensorEquiv Q`: for an algebra `Q` over the residue field `k` of `R`, `k ⊗_R Q ≃ Q`.
- `goodChartStatement`: let `A` be of finite type over the discrete valuation ring `R` and `J` the
  intersection of a non-empty family of specialization primes of points of ramification index one.
  These primes contain the maximal ideal of `R`, so `A ⧸ J` is an algebra of finite type over the
  residue field `k`. It is non-zero: `J` lies in a member of the family, a prime ideal, so
  `J ≠ A` (this is where non-emptiness is used). `A ⧸ J` embeds into the product of the residue
  fields of the given points, which are geometrically reduced over `k`; hence `A ⧸ J` is
  geometrically reduced (`GoodChartAlgebra.isGeometricallyReduced_of_forall_eq_zero`).
  `exists_free_smooth`, applied to the non-zero algebra `A ⧸ J` and the module
  `(A ⧸ J) ⊗_A Ω_{A/R}`, gives a prime `q` and `r₁, r₂ ∉ q`; a lift `s ∈ A` of `r₁ r₂` lies
  outside `J` (as `r₁ r₂ ∉ q`), so `D(s)` meets the centre, and over `A[1/s]` the centre is smooth
  over `k` and the restricted differentials are free.

This is Bosch–Lütkebohmert–Raynaud, *Néron Models*, §3.3, Lemma 4 (printed p. 67) and the density
of the smooth locus used in §3.4 (printed p. 71).
