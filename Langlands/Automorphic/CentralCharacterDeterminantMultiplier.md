# Actual determinant multiplication between specified central-character spaces

Author: Worker 2. This internal construction works on the existing continuous
complex rational-invariant functions for every number field `F : Type u` and
every natural rank, including zero. Both characters `χ` and `ω` are arbitrary
continuous Hecke characters. Finite order and unitarity are not required.

`AdelicGL.determinant_scalar` specializes the pinned Mathlib determinant of a
scalar invertible matrix to the actual full adelic group. For an actual idele
`z`, its value is `z^n`. Pulling back a Hecke character gives
`HeckeCharacter.adelicDeterminant_scalar`: the scalar multiplier at that matrix
is `χ([z])^n`.

The existing central-character condition has the convention
`f(scalar(z) g) = ω([z]) f(g)`. Applying actual multiplication by `χ(det g)`
and the scalar determinant formula proves
`centralCharacter_determinantMultiplier`: the resulting character is
`χ^n * ω`. The proof uses only multiplication of these actual character values;
neither an inverse character convention nor a positive-rank assumption is
introduced.

The inverse multiplier takes the target central-character space back into the
source because `(χ⁻¹)^n * (χ^n * ω) = ω`. Actual inverse cancellation therefore
proves equality between the image of the source submodule and the target
submodule.
`CentralCharacterFunctions.determinantMultiplier` restricts the published
continuous complex-linear equivalence to these two existing carriers, with
their inherited subtype topologies.

The underlying ambient function, forward evaluation, inverse evaluation, and
full right-translation covariance formulas are proved. The covariance remains
`R(g) Mχ = χ(det g) Mχ R(g)`, with source central character `ω` and target
central character `χ^n * ω`.

The provenance is a direct internal restriction of `DeterminantMultiplier`
using the central-character spaces of `Ambient` and Mathlib's
`Matrix.GeneralLinearGroup.det_scalar` and continuous-linear submodule
restriction. No new original-literature comparison is claimed.
This unit does not assert smoothness, growth, automorphic or cuspidal
preservation, existence of nonzero vectors, or central-character invariance
under arbitrary equivalence of embedded realizations.
