# Infinitude from a nontrivial valuative relation

This internal derived helper is work of Worker 97 for Task 5397. It exposes
the elementary infinitude argument already used privately in the published
`Langlands.GroupScheme.Rational.ReductiveSpectralBoundednessReduction`
module. No new literature input is required.

For a field `K` with a nontrivial `ValuativeRel`, Mathlib supplies an element
`c` of its value group with `0 < c < 1`. Surjectivity of the canonical
valuation lifts `c` to an element `a` of `K`. If two natural powers of `a`
are equal, applying the valuation gives equal powers of `c`. The published
ordered-group power-injectivity theorem makes the exponents equal. Thus
the powers of `a` give an injection from the natural numbers into `K`,
and `K` is infinite.

`NontrivialValuationInfiniteStatement` is the Prop-valued statement of this
fact at arbitrary universe `u`; `nontrivialValuationInfinite` proves it.
The direct local-field corollary uses the nontrivial valuative relation
already contained in `IsNonarchimedeanLocalField`. It requires no
characteristic restriction and no additional hypothesis on the local
field.

This supplies the `Infinite K` instance needed to apply the actual split-torus
rank lower bound in the quaternionic spin proof: it can be introduced locally
with `let : Infinite K := infinite_of_isNonarchimedeanLocalField K`.
The module adds no global instance and does not prove the rank bound or
`LocalSpinRankOneStatement`.
