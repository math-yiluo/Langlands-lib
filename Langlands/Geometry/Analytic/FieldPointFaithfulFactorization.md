# Factorization through faithful full field-point test sources

This internal module works over a complete ultrametric normed field `K`
and a normed extension field `L`. The algebra universe, the small
space universe and the extension-field universe are independent.
The original affinoid spectra must be small in the chosen space
universe `v`.

For a bounded character `χ : R → L`, `sourceMap χ` is the actual
strong map from the saturated spectrum of `R / ker χ` to the
small saturated spectrum of `R`. It is induced by the presented
closed-quotient map. The quotient spectrum retains smallness by
its injective comap into the original spectrum.

For a bounded map `φ : S → R` and characters with `χ ∘ φ = ψ`,
`sourceMap_naturality` proves that first mapping the faithful test
source to the original spectrum of `R` and then along `φ` equals
first mapping to the faithful test source of `ψ` and then to the
original spectrum of `S`. This is equality of entire strong
morphisms. The proof applies exact composition preservation of
the small-spectrum map to the previously proved equality between
the descended map composed with the quotient of `S` and the
quotient of `R` composed with `φ`.

Under completeness of `L` and the explicit
`DomainCompletedResidueSurjectivityStatement`, the faithful full
test point maps along `sourceMap χ` to the full field point of
`χ` on the original small spectrum. The proof uses full-field-point
naturality of small-spectrum maps and the exact factorization of
`χ` through its kernel quotient. The conclusion retains all chart
evaluations and their restriction compatibility.

The provenance is internal: this module combines the actual quotient
and restriction maps with the small-spectrum functor and its full
field-point naturality. It supplies factorizations for local
representatives without asserting localized pullback preservation.
