# Actual positive Lie and dimension moduli presheaf

This module constructs the actual presheaf of rational algebra-action
classes admitting a single representative with the prescribed geometric
dimension and positive Lie compatibility. It is derived infrastructure
for Harris–Taylor (2001), III.1, printed pp.89–91 / PDF pp.97–99, in the
registered source `harris-taylor-2001-geometry-cohomology-simple-shimura`
(SHA256 `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`).
The source's compatible actions and dimension requirement motivate the
joint predicate. Its polarized level moduli problem has further data;
the present presheaf retains the abelian scheme and rational action.

K is a number field. L is an imaginary quadratic number field mapping
to K. E is a number field mapping to K, and A is a rational algebra with
a K-algebra structure. The intended application takes E to be the totally
real central field, but this pullback construction does not require total
reality. All scheme and algebra carriers in this module are at universe
zero; the class-valued presheaf takes values in `Type 1`.

For s : S → Spec K and n : ℕ, `DimensionLieCondition` is the conjunction
of geometric relative dimension `[E : ℚ] * n^2` and the actual positive
Lie tensor-sheaf condition: local rank n and equality of the structural
and action-induced E-scalars. `DimensionLieActionClassCondition` requires
one representative satisfying both conditions. The quotient is the actual
rational algebra-action quotient; equality retains an invertible rational
homomorphism and equivariance for every A-element.

`lieCompatibilityClassCondition_pullback` descends the proved actual
positive Lie pullback theorem to rational action classes. This first
lemma does not need E to be a number field. With that hypothesis,
`dimensionLieCondition_pullback` combines actual prescribed geometric
dimension pullback with `lieCompatibility_pullback` on the same actual
base-changed abelian scheme and pulled-back algebra action.
`dimensionLieActionClassCondition_pullback` chooses the one joint witness
already supplied by the source class and pulls back that precise witness.
It therefore does not need dimension invariance under arbitrary rational
isomorphisms, and does not replace the dimension and Lie witnesses by
unrelated representatives. The canonical Lie naturality used underneath
is already proved; no output naturality or comparison assumption is
supplied by the caller.

`dimensionLieActionSubfunctor` restricts the actual
`RationalAlgebraAction.isoClassOverPresheaf` on `(Over (Spec K))ᵒᵖ` to this
joint image. The map-stability field uses the proved pullback theorem
and the structural equality in the over category.
`dimensionLieActionPresheaf` is its actual subtype-valued functor;
identity and composition follow from the ambient actual quotient
presheaf through the standard subfunctor construction.
`dimensionLieActionPresheafInclusion` is the natural inclusion into the
ambient rational action classes and is injective at every base scheme.
The object and map formulas identify its values with the previously
constructed joint image classes and its maps with actual rational-action
pullback, including the formula on a satisfying representative.

The bases and morphisms are arbitrary schemes over K, with no
reducedness, flatness, geometric-point, connectedness, or Noetherian
restriction. This broader base-change infrastructure does not assert
representability. Construction of polarized level data under arbitrary
base change, the source trace-character equivalence, scheme
representability, scheme level maps and coefficient descent remain
separate obligations.
