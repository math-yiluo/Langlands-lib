# Cotangent base change and actual weights

This is an internal helper for the published
`CoordinateWeightDecompositionStatement`; it is derived from the actual
coordinate and cotangent models, with no additional representation hypothesis.
It does not itself prove the decomposition statement.

`baseAugmentation_eq` identifies the actual identity augmentation after
coefficient extension with the tensor extension of `Lie.coordinateOrigin`.
The latter is split surjective through the scalar algebra map, so Mathlib's
`Algebra.TensorProduct.lTensor_ker` identifies the actual base ideal with the
extended augmentation ideal. `cotangentTensorEquiv` composes Mathlib's
`Ideal.tensorCotangentEquiv` (flat base change over a field) with the equivalence
induced by this ideal equality. Its pure-tensor formula is
`a ⊗ q ↦ a • cotangentBaseChange q`.

`characterValue_affineMap` derives naturality from the existing multiplicative
group point equivalence. Evaluating an actual eigenfunction at the extended
universal coordinate point then gives the pure tensor formula
`actionCoordinates b s f = characterValue χ s ⊗ f`.
Applying the actual ideal quotient map proves that `cotangentMk` carries each
augmentation eigenspace into the cotangent eigenspace with the same character.
All coefficient algebras are retained, the field and its characteristic are
arbitrary, and no finite-dimensionality assumption is used.
