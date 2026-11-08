# Actual relative witnessed generators under unitary Hecke twisting

This internal construction transforms a supplied actual relative witnessed
generator by an actual globally unitary Hecke character whose finite component
is the prescribed local modulus-one quasi-character. It retains explicit
inputs for the cuspidal determinant multiple, its weak association, and the
local transfer reciprocity identity. It proves no existence assertion for
those inputs and does not prove the final relative isometry operation
statement.

The finite determinant calculation uses the published identity for the
determinant of the actual local matrix insertion. Thus the restricted adelic
determinant character is precisely the finite Hecke component applied to the
local determinant. The prescribed component equality then identifies the
local twist with the exact character twist used in the isometry target.

The relative reciprocity character is the inverse of the Hecke character
composed with transfer. Local transfer reciprocity is also expressed using
inverse geometric reciprocity. These two inverses cancel, giving the exact
continuous local Weil character specified by the chosen geometric reciprocity
candidate. Global unitarity gives modulus one for the relative scalar
character without requiring continuity of that global character separately.

The supplied determinant-multiple presentation provides an actual local
representation equivalence. Scalar twisting preserves irreducibility and
admissibility. Admissibility is transported through the proved canonical
local topology comparison. The genuine unitary supercuspidal support twists
by the established support transport and then passes through the actual
local equivalence.

The resulting `WitnessedGenerator.heckeTwist` has the same rank, place above
the finite place, reciprocity candidate over that place and characterized
local map. Its Weil representation is the actual scalar twist on the whole
original carrier. Its continuity comes from the supplied weak association.
The full local exact expansion twists using the local restriction identity;
no semisimplification is substituted. The Weil and automorphic elements are
the exact two unitary lattice twists required by the published target.

The provenance is internal composition of published concrete constructions
and proved representation transport results. The global extension, cuspidal
twist existence and association propositions remain separate proof
obligations, as does local transfer reciprocity when not supplied.

The local determinant restriction identity reuses `HeckeCharacter.finiteLocalDeterminant_eq_finiteComponent_det` from `Langlands.Automorphic.LocalDeterminantCharacter`.
