# Real approximation for induced tori

`InducedTorusRealApproximationStatement` asserts that the rational points of
an affine induced torus over `ℚ` are dense in its actual real points with
the affine evaluation topology. This is the induced-torus case of Milne,
*Algebraic Groups* (2017), Theorem 25.70, p. 564.

`WeilGmRational.hasRealApproximation` proves density for the Weil restriction
of the multiplicative group along any finite commutative rational algebra.
A finite basis gives the published determinant-open chart in affine space.
Affine space has real approximation, and its affine open subscheme inherits
it by open immersion.

`inducedTorusRealApproximation` uses the finite Galois splitting field from
the induced-torus hypothesis. The published decomposition identifies the
torus with the Weil restriction of the multiplicative group from a finite
product of intermediate fields. The isomorphism of the underlying schemes
over `Spec ℚ` transfers real approximation, including for the empty product.
