# Actual fpqc covers for unramified integer coefficients

This internal construction specializes `valuationInteger_fpqc` and
`valuationIntegerCover` to the actual integer maps used for integral-model
descent. It also proves the fpqc property for the actual intermediate
coefficient algebras inside the maximal-unramified integers.

For a nonarchimedean local field `F`, `integerMap_fpqc` proves that
`Spec (extensionIntegers F E) → Spec (baseIntegers F)` is surjective,
flat and quasi-compact for every intermediate field `E` in the separable
closure. This fact does not require `E/F` to be finite or unramified.
The proof uses the spectral valuation extending the norm valuation.

`fixedFieldIntegerMap_fpqc` proves the same properties for the actual map
`Spec (fixedFieldIntegers F) → Spec 𝒪[F]`, whose ring map is
`integerToFixedField F`. `fixedFieldIntegerCover` is the corresponding
singleton fpqc cover. Its map is identified exactly by
`fixedFieldIntegerCover_f`.

More generally, `integerSubalgebra_fpqc` applies to any
`𝒪[F]`-subalgebra `T` of `fixedFieldIntegers F`. Its flatness follows
from torsion-freeness over the base valuation ring, which is a Bezout
domain. Its spectrum map is surjective because the surjective map from
the maximal-unramified integer spectrum factors through it. As a map
between affine schemes, it is quasi-compact.
`integerCoefficientsCover` packages the specialization to the actual
subalgebra `integerCoefficients F E` as a singleton fpqc cover, with
its exact map given by `integerCoefficientsCover_f`.

These are cover constructions and proofs of properties of actual maps.
They do not supply a semilinear family, descent datum or descended model.
