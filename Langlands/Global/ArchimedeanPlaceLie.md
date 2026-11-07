# Per-place factors of the actual archimedean Lie algebra

This module constructs projections and injective insertion maps for every
real and complex place of a field `F : Type u`, using the existing mixed
coordinates of the actual archimedean matrix Lie algebra. The rank `n` is
any natural number. Only the final finite-sum reconstruction needs the
number-field hypothesis.

`realPlaceLieProjection` takes values in `n` by `n` real matrices.
`complexPlaceLieProjection` takes values in `n` by `n` complex matrices
regarded as a real Lie algebra. Both brackets are the matrix commutator.
The maps evaluate the original mixed coordinates at the indicated place;
they preserve the bracket because entrywise scalar evaluation is an
algebra homomorphism.

`realLiePlaceCoordinates` identifies the genuine `RealLieAlgebra F n` with
the product of the two families of these matrix Lie algebras. Its inverse
assembles each matrix entry from its real-place and complex-place
coordinates. Both inverse identities and linearity hold by the coordinate
definitions, and bracket compatibility follows from that of each
projection.

`realPlaceLieInclusion` and `complexPlaceLieInclusion` insert a matrix in
one selected factor and zero in all the others. They use the inverse of
the preceding Lie equivalence and the single-coordinate linear map,
whose bracket compatibility is proved pointwise. The projection formulas
recover the inserted matrix at its own place and give zero at all other
places. In particular, both insertion maps are injective.

`realPlaceComplexLieInclusion` and `complexPlaceComplexLieInclusion` are
the complex-linear extensions of these actual real Lie inclusions:

```text
ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ →ₗ⁅ℂ⁆ ComplexLieAlgebra F n
ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ ComplexLieAlgebra F n.
```

Their pure-tensor formulas retain the indicated inserted real direction.
The second domain complexifies the full underlying real Lie algebra of
complex matrices; it does not discard either real direction at a complex
place. Injectivity follows from the already proved real insertion
injectivity by flat scalar extension.

For a number field, `sum_placeLieInclusions` expresses every original real
Lie direction as the finite sum of its place projections inserted back
into the global algebra. Its proof applies the coordinate Lie equivalence
and computes each coordinate using the projection formulas.

This is an internal construction from `ArchimedeanLieAlgebra`, the
published mixed completion coordinates, and pinned Mathlib's associative
Lie algebras, products, single-coordinate maps and scalar extension. It
uses no new original-literature assertion. The coordinates retain the
existing choice of representative embedding at a complex place.

These maps describe genuine factors of the original Lie algebra. They do
not extract irreducible local factors from an automorphic representation,
construct an archimedean globalization or Langlands parameter, or define
attached local L/epsilon factors.
