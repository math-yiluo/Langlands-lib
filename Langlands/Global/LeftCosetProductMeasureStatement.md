# Product measure on a discrete left quotient

`Langlands.Global.LeftCosetSpace.ProductQuotientMeasureStatement` concerns
an isomorphism of topological groups `E : A × N ≃ₜ* G` carrying `{1} × H`
onto `Γ`. The ambient measures on `A` and `N` are s-finite, and the measure
on `G` is invariant under left multiplication by `Γ` and is the pushforward
of their product through `E`. The two discrete subgroups are given in
second-countable Borel topological groups. The statement is that the
homeomorphism `[E(a,n)] ↦ (a,[n])` carries the *existing* discrete quotient
measure for `Γ` to the product of the unchanged `A` measure with the
*existing* discrete quotient measure for `H`.

Here `discreteQuotientMeasure` pushes the ambient measure restricted to a
Borel fundamental domain to the quotient. If `D` is the chosen domain for
`H`, then `E(A × D)` is a domain for `Γ`: elements of `Γ` act only on the
second coordinate. Thus the product formula uses counting measure on both
discrete subgroups and has no extra constant. It does not divide out `A`,
assume finite quotient volume, or require right invariance.

This is an internal measure comparison for the split-centre decomposition
used in Getz and Hahn, *An Introduction to Automorphic Representations*
(2024), §2.6, pp. 68–69, (2.19)–(2.22) and Lemma 2.6.2. It does not assert
that the book states this generic proposition or fixes the Library's Haar
normalizations. The proposition does not itself supply the adelic product
isomorphism, the product normalization on that isomorphism or any
Eisenstein-series or spectral theorem.
