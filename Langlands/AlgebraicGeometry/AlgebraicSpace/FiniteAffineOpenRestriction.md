# Quasi-affine sources over compact universal-open restrictions

Author: Worker 133.

This internal module constructs the actual scheme source of an open
restriction of a finite map and proves the quasi-affineness needed for
the finite-surjective AF descent reduction. The base scheme is arbitrary.

## Actual restricted source

In namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteAffineOpenRestriction`,
start with an actual scheme `U : Over S`, an algebraic space `Y`, a
presheaf map `π : (schemeYoneda S).obj U ⟶ Y.presheaf`, and a subfunctor
`A` whose inclusion in `Y.presheaf` is a representable open immersion.

`sourceOverOpen π A hA` is the actual scheme representing the inverse
image of this open in `U`. `toSource` is its actual morphism over `S` to
`U`, and `toOpen` is its actual presheaf map to `A.toFunctor`.
`sourceOverOpen_square` is their cartesian square.

`toSource_isOpenImmersion` applies the represented open-immersion
predicate. `toOpen_isFinite` and `toOpen_isSurjective` separately prove
that the restricted transformation retains finiteness or geometric
surjectivity from `π`, by base change. `range_toSource` identifies its
Yoneda image in the source with `A.preimage π`.

## Quasi-affineness after compact shrinking

For an actual affine source open `V`, assume `A` lies in the target
subfunctor `universalAffineOpen π V` constructed in
`FiniteAffineUniversalNeighborhoods`.
`exists_toAffine` proves that `toSource` factors as an actual scheme
morphism through `V` over the original base. Its implemented proof uses
the universal-image adjunction, `range_toSource`, and evaluation at the
identity source test.

`sourceOverOpen_isQuasiAffine` additionally assumes that `π` is finite
and that the actual open algebraic subspace associated to `A` is
quasi-compact. It proves that the restricted source scheme is
quasi-affine, in Mathlib's convention including quasi-compactness.
Neither source surjectivity nor target quasi-separatedness is required
for this conclusion.

The proof uses `OpenSubspaceGeometry.compactSpace_of_finite_source` to
make the restricted source compact. The factorization through `V` is
an open immersion: its composite with `V`'s inclusion is the open
immersion `toSource`, so Mathlib's open-immersion cancellation lemma
applies. The compact source is therefore immersed in an affine scheme,
and `Scheme.IsQuasiAffine.of_isImmersion` gives quasi-affineness.

All constructions and proofs are internal consequences of the named
Library and Mathlib APIs. The result does not assert affineness of the
restricted source or quasi-affineness of the target. The independent
quasi-affine-source AF descent theorem and the final scheme gluing and
finite-set AF arguments remain obligations of the full task.
