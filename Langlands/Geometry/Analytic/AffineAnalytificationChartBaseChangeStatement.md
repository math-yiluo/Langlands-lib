# Fixed-radius ground field comparison for affine analytification

`AffineAnalytification.AffineAnalytificationChartBaseChangeStatement` states
an isomorphism of actual presented affinoid algebras for each positive
polyradius. Let `K` and `L` be complete nontrivially normed ultrametric fields
with `NormedAlgebra K L`, so the structural map is isometric. Let `A` be a
commutative `K`-algebra with finite polynomial presentation `P`, and put
`Q := baseChangePresentation K L P`, the published presentation of
`L ⊗[K] A` over `L` by the generators `1 ⊗ xᵢ`. The field universes and the
universe of `A` are independent. The extension need not be algebraic.

For any positive polyradius `r` on the generator indices of `P` (the same
indices for `Q`), put `B := PolynomialLocus.chart P r`. The proposition
asks for a bounded `L`-algebra equivalence

```
PresentedAffinoidAlgebra.GroundFieldExtension.algebra K L B
  ≃ PolynomialLocus.chart Q r
```

such that for each `a : A`, the image of `iota (algebraMap P r a)` is
`algebraMap Q r (1 ⊗ a)`. In particular, the equivalence respects the
specified maps from the original coordinate algebra, not just the two
abstract quotient Banach algebras. This compares affinoids at the *same*
polyradius, not necessarily at the same index of the two fields' chosen
radius exhaustions. The nontrivial-norm hypotheses are those of the
existing `baseChangePresentation` declaration used here.

This is a derived chart-level step toward the usual scheme comparison
mentioned in Conrad–Temkin, *Non-archimedean analytification of algebraic
spaces* (2009), Theorem 2.3.5, printed p. 13 (PDF p. 13), registered as
`conrad-temkin-2009-nonarchimedean-analytification`. Conrad uses that
compatibility in the last paragraph of the proof of Proposition 5.11(3)
in *Weil and Grothendieck approaches to adelic points* (2011), p. 19,
registered as `conrad-2011-weil-grothendieck-adelic-points`. Neither source
formulates this particular assertion about the two Library quotient
presentations. This module states the fixed-radius comparison; gluing it
across cofinal radius exhaustions and comparing the localized
analytifications remain separate steps.
