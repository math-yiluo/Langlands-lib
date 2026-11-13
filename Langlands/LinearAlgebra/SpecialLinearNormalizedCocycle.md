# Normalization of projective special-linear conjugation cocycles

Author: Worker 239.

This derived internal matrix-algebra unit removes the projective scalar
ambiguity from conjugating matrices that preserve a supplied coordinate line.
It works over any commutative ring and finite decidable matrix index type;
the acting group and coefficient ring have independent universes.

`PreservesCoordinate p X` means that column `p` of `X` is zero away from its
diagonal entry. Multiplication in this column has one summand. Applying this
to `X⁻¹ X` shows that `X p p` is a unit. `coordinateScalar` chooses that unit,
and `normalize` divides the matrix by it. The normalized matrix fixes the
coordinate vector indexed by `p`, and its conjugation on `SL` is unchanged.
The same conjugation identity holds after any coefficient homomorphism.

`normalize_cocycle` assumes a group acting by ring automorphisms, a family
`x σ` preserving this coordinate line, and equality of conjugation on `SL`
for `x (σ τ)` and `x σ * map σ (x τ)`. It proves the honest cocycle identity
for the normalized family. Its proof compares the conjugations, uses
normalization to make the selected diagonal entries equal to one, and
applies the scalar-ambiguity criterion from `SpecialLinearConjugationScalars`.

This is a direct derivation from the scalar criterion, matrix multiplication,
and the group identities. It asserts no existence of an invariant coordinate
line, no Hilbert 90 trivialization, and no Hermitian group presentation.
