# Minimal generators of a local maximal ideal

This internal supporting module provides the coefficient detection needed for
the Koszul comparison proof of the residue-field projective-dimension lower
bound. It derives its results from the cotangent-space and Nakayama interfaces
in the pinned Mathlib.

For a finite tuple in the maximal ideal whose images in the cotangent space
are linearly independent over the residue field, a linear combination in the
square of the maximal ideal has every coefficient in the maximal ideal.
The proof maps the combination to the cotangent space, changes scalar
multiplication to residue-field scalar multiplication, and applies linear
independence.

For a Noetherian local ring, `exists_minimalMaximalIdealGenerators` lifts a
cotangent-space basis to the maximal ideal. The tuple is indexed by the
`spanFinrank` of that ideal, its elements generate the ideal as a module,
and its cotangent images are linearly independent. The generator statement
follows from Mathlib's cotangent-space spanning equivalence, which uses
Nakayama. This module does not assert the projective-dimension bound.

`minimalMaximalIdealGenerators` chooses such a tuple. Its spanning,
independence, and coefficient-detection properties are supplied by the
three theorems with the corresponding suffixes.
