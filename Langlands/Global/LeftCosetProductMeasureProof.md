# Exact product measure on a discrete left quotient

`Langlands.Global.LeftCosetSpace.productQuotientMeasure` proves
[`ProductQuotientMeasureStatement`](LeftCosetProductMeasureStatement.md).
The quotient homeomorphism sends `[E(a,n)]` to `(a,[n])` and carries the
discrete quotient measure for `Γ` to the product of `μA` and the discrete
quotient measure for `H`.

Let `D` be `fundamentalDomain H hHdisc` and put `S = E(A × D)`. The Borel
measurable equivalence underlying `E` makes `S` measurable. For each point
`E(a,n)`, `fundamentalDomain_unique` gives a unique `h : H` with `h * n ∈ D`.
The subgroup correspondence expresses every element of `Γ` uniquely as
`E(1,k)` for `k : H`. This element sends `E(a,n)` into `S` exactly when
`k * n ∈ D`. The resulting uniqueness of the translate gives the
`IsFundamentalDomain` witness for `S`.

The assumed left `Γ`-invariance of `μG` lets `discreteQuotientMeasure_eq`
compute the quotient measure with `S`. The measure-preserving hypothesis
on `E` and `MeasurableEmbedding.restrict_map` identify `μG` restricted to
`S` with the pushforward of `(μA.prod μN)` restricted to `A × D`.
Composing the pushforwards through `E`, `mk Γ`, and the quotient
homeomorphism gives the pushforward by `Prod.map id (mk H)`, by
`productHomeomorph_mk`. The product restriction is `μA.prod (μN.restrict D)`.
Mapping its second factor by `mk H` gives `discreteQuotientMeasure H hHdisc μN`
by definition. This gives the measure identity with counting normalization
and no scalar factor.

## Provenance

This internal comparison combines the Library's product homeomorphism and
discrete quotient measure. Its adelic motivation is the factorization by
the positive split centre and the norm-one group in Getz–Hahn, *An
Introduction to Automorphic Representations* (2024), §2.6, (2.19)–(2.22)
and Lemma 2.6.2, printed pp. 68–69 (PDF pp. 85–86). Section 3.6, printed
p. 90 (PDF p. 106), describes the counting normalization for `G(F)` on
the full and norm-one adelic quotients. The registered source is
`getz-hahn-2024-automorphic-representations` (SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`).
