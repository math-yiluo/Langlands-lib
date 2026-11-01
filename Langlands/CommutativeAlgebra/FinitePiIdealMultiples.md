# Ideal multiples of finite coordinate modules

`coordinateIdealSubmodule I` is the submodule of vectors whose coordinates
all belong to `I`, defined by Mathlib's `Submodule.pi`.

This internal supporting module identifies an ideal multiple of a finite
coordinate module with the vectors whose coordinates lie in the ideal.
Projection to each coordinate proves one direction. Expressing a vector as
a finite sum of single-coordinate vectors proves the other direction.
The equality `ideal_smul_top_eq_coordinateIdealSubmodule` packages that
identification as an equality of submodules. The square-ideal lemma applies the same result to the square of the ideal, using
associativity of ideal multiplication and submodule scalar multiplication.

These elementary derived results supply the coordinate interface for the
Koszul detection condition in the residue-field projective-dimension proof.
They impose no local or Noetherian hypotheses and assert no dimension bound.
