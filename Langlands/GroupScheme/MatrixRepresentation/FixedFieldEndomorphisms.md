# Fixed-field algebra from normalized geometric character lines

Worker 537, using unchanged support by Workers 666 and 539.

This module packages a supplied scalar-action construction into a `k`-algebra
homomorphism from a stabilizer fixed field to the original matrix algebra.
The supplied family `F` must act on every conjugate of a vector `v` through
the corresponding conjugate of the scalar. The conjugate lines must span.
These action formulas force preservation of zero, one, addition, multiplication,
and the original field scalars. The map is injective when a coordinate index
exists.

When `v` has a coordinate equal to one, is fixed by the subgroup `H`, and spans
a geometric character space, the range is precisely the actual endomorphisms,
provided each supplied `F a` is an actual endomorphism. Any original endomorphism
preserves the character line, so acts there by some scalar `a`. Its original
entries commute with coefficientwise automorphisms. The normalized coordinate
and `H`-fixed vector show `a` lies in the fixed field. The endomorphism's action
on all conjugate lines then identifies it with `F a`.

For the representation theorem, the scalar-action family is constructed:
`GaloisOrbitScalars.orbitValue` transports an element of the stabilizer fixed
field equivariantly around the weight orbit.
`exists_intertwiner_with_weight_scalars` descends the corresponding diagonal
operator to an actual original-field endomorphism.
`exists_normalized_galois_characterLine` supplies the normalized fixed line.
The algebra packaging and image argument then give
`exists_fixedField_endomorphismAlgHom_of_weightOrbit`.

For a multiplicative-type group over a separable closure, the published
diagonalizable splitting theorem gives character-space spanning, and the
single-orbit theorem identifies the weights with the orbit of the supplied
weight. This proves
`exists_fixedField_endomorphismAlgHom_of_isMultiplicativeType`, exactly the
endomorphism conjunct of the target, with no further assumptions. This last
theorem retains every field, group, affine-test, and stabilizer hypothesis of
that conjunct.

This is a derived proof of the endomorphism conclusion in Milne,
*Algebraic Groups* (2017), Theorem 12.30, printed pages 241–242 (PDF pages
257–258), registered source `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The proof uses actual all-algebra character spaces throughout. It uses the
general coefficientwise fixed-vector argument in place of selecting a finite
Galois splitting field.
