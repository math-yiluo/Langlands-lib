# Finite rational tensor comparison target

Author: Worker 36.

`FiniteRationalTensorComparisonStatement` says that for a finite bounded
map `φ : P → Q` between the actual presented strict affinoid algebras,
and chosen rational data `d` over `P`, the canonical map

`d.tensorComparison φ : d.algebraicBaseChange φ →+* (d.pullback φ).algebra`

is bijective. Here finiteness is precisely
`φ.toAlgHom.toRingHom.Finite`, so the finite module structure on `Q` is
the one induced by this given map. The ordinary algebraic tensor product
uses the actual maps `d.baseMap` and `φ` as its scalar structures.
The target is the constructed quotient for the pulled-back rational
equations. On a pure tensor `a ⊗ b`, the map is
`d.comparison φ a * (d.pullback φ).baseMap b`.

The coefficient field is complete and ultrametric. Its valuation may be
trivial. The rational data have the existing unit radii, and their denominator
and numerators have no common zero on the spectrum. Empty numerator tuples
and zero quotients remain allowed. The conclusion concerns the bijectivity
of this exact canonical ring map. It imposes no topology on the ordinary
algebraic tensor product.
The declaration defines a proposition and supplies no proof.

This is a derived specialization of Berkovich, *Non-archimedean analytic
spaces* (Trieste lectures, 2009), Definition 2.1.7 and Fact 2.1.8(iii),
printed/PDF p. 8. Those passages identify ordinary and completed tensor
products when a module is finite. Exercise 2.1.9(ii), on the same page,
identifies finite algebras with finite Banach algebras. Apply this framework
to the finite `P`-algebra `Q` and the rational `P`-affinoid algebra
`d.algebra`; the commutative tensor symmetry puts the factors in the
order used here. Exercise 2.2.2(ii), printed/PDF p. 9, gives the rational
quotient equations whose pullback realizes this completed base change.
Identifying the resulting isomorphism with the constructed canonical map
requires its factor equations. This statement records that resulting
comparison as a separate proof obligation.

The existing dense-range theorem for `d.tensorComparison φ` supplies
neither injectivity nor surjectivity. The bounded rational pushout property
also does not alone identify the ordinary tensor product with this
complete quotient. A proof must establish the finite tensor comparison
or an equivalent argument, including the stated trivial-valuation case.
This target supplies local infrastructure for later finite and étale
restriction results; it does not formulate an analytic étale site.

Registered source: `berkovich-2009-trieste-analytic-spaces`, retained PDF
SHA256 `8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
