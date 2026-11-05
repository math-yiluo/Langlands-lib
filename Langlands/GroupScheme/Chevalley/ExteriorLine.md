# The exterior line of a split subspace

This internal linear-algebra construction implements the mechanism behind
Milne, *Algebraic Groups* (2017), Lemma 4.28, over arbitrary commutative
coefficient rings.

For a finite basis and an injectively indexed selection of `d` basis
vectors, `coordinateSpan` is their actual submodule span and
`exteriorLineVector` is their decomposable `d`th exterior product. The
annihilator of this exterior vector under multiplication by degree-one
vectors in the exterior algebra is exactly `coordinateSpan`.

One direction uses the repeated-vector relation in the exterior algebra.
For the other direction, append a vector to the selected tuple and pair its
exterior product with the corresponding dual coordinates, preceded by a
dual coordinate outside the selection. The determinant of this pairing
recovers that outside coordinate of the appended vector. Vanishing
therefore kills every outside coordinate, which is exactly membership in
the chosen subspace. The argument includes `d = 0` and imposes no
reducedness, domain or field assumption on the coefficient ring.

`preserves_coordinateSpan_iff` is the line-stabilizer equivalence for an
invertible linear map. Preservation of the subspace expresses the exterior
image as a scalar multiple of its exterior vector, by the determinant
identity for a top-degree alternating map on the selected subspace. A dual
exterior coordinate takes value one on that vector. Applying the inverse
exterior map and this coordinate proves that the scalar is a unit.
Conversely, the exterior algebra map preserves products; the unit scalar
can be cancelled in the annihilator equation, recovering subspace
preservation from the proved annihilator characterization.

The public helper `alternatingMap_eq_det_smul` expresses any top-degree
alternating map as the basis determinant times its value on the basis. It is
also reused by `Dynamic/AdjointDeterminantLine`.
