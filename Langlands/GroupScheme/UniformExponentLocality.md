# Locality of uniform exponents

This internal reduction supports the proof of SGA 3, Exposé IX, Lemma 6.1.
It introduces no flatness, separation or affineness hypothesis on the group.
`AffineStatement` is the original target restricted to an affine base; the
final theorem derives the unchanged published quasi-compact-base target from it.
The affine proposition remains a hypothesis in this module.

The proof identifies the exponent equation on all scheme-valued points with
equality of the multiplication morphism and the constant unit homomorphism
`G → S → G`, the zero homomorphism in additive notation. Such an exponent
survives arbitrary base change and any positive multiple. Given a positive
exponent on an open neighborhood of every base point, quasi-compactness
supplies a finite subcover. The product of its exponents is a common positive
multiple. Equality of multiplication by this product with the constant unit
homomorphism glues by the published pointwise étale locality of group-scheme
homomorphism equality. For an empty base the empty product is one.

For the affine reduction, restrict the original group to an affine open
neighborhood of each base point. Local finite presentation,
quasi-compactness, quasi-separatedness and local quasi-finiteness all survive
base change. Apply `AffineStatement` there, then use the finite-cover argument.

The proof is an internal categorical elaboration of the finite affine-cover
step in SGA 3, Exposé IX, Lemma 6.1, footnote 40, printed p.53 (retained PDF
p.23), registered as `sga3-expose-ix-gille-polo-2009`, SHA256
`7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`.
It reuses the Library multiplication maps, base-change point equivalence and
fppf homomorphism locality. It does not prove existence of the affine exponent.
