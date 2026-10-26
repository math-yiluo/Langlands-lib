# Algebraic tensor comparison for actual rational base change

Author: Worker 36.

For a bounded map `φ : P → Q` of presented strict affinoid algebras and
rational data `d` over `P`, this derived construction forms the ordinary
algebraic tensor product `d.algebra ⊗[P] Q` using the scalar structures
induced by the actual maps `d.baseMap` and `φ`. Its commutative ring and
two factor maps are constructed, and the factors agree on `P`.

`tensorComparison` is the canonical ring map from this tensor product
to the actual pulled-back rational quotient `(d.pullback φ).algebra`.
It uses the published bounded maps `d.comparison φ` and
`(d.pullback φ).baseMap`. Its two factor formulas are proved, so on a
pure tensor `a ⊗ b` it is `d.comparison φ a * (d.pullback φ).baseMap b`.
No tensor comparison is an input.

The comparison has dense range. First the published monomial-expansion
density of denominator-clearing fractions is transported from the relation
model to the rational quotient of an arbitrary presented base. The
denominator is a unit in `d.algebra`, by the published unit-ideal theorem
applied to the original rational data. Its inverse supplies a preimage of
the mapped denominator's inverse. Thus every element `x` of the target
whose product with a power of that denominator lies in the base image
has the explicit tensor preimage `s^r ⊗ b`, where `s` is the original
denominator's inverse and the denominator-clearing equation uses `b : Q`.
These fractions are dense, giving `denseRange_tensorComparison`.

The hypotheses are a complete ultrametric normed coefficient field and
the existing chosen unit-radius rational presentations. No nontrivial
valuation or module finiteness is assumed. The empty variable tuple and
zero quotient remain allowed. No norm or topology is put on the ordinary
algebraic tensor product.

This is derived infrastructure for the finite Banach base-change
comparison in Berkovich, *Non-archimedean analytic spaces* (Trieste
lectures, 2009), Definition 2.1.7 and Fact 2.1.8(iii), printed/PDF p. 8.
The actual rational quotient equations come from Exercise 2.2.2(ii),
printed/PDF p. 9. The present result does not prove Fact 2.1.8(iii):
injectivity, surjectivity under finiteness, finite Banach comparison and
analytic finite-étale base change are separate obligations.

Registered source: `berkovich-2009-trieste-analytic-spaces`, retained PDF
SHA256 `8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
