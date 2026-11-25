# Actual stabilized Grassmannian jets and Lie determinant-dual ampleness

This module assembles the complete actual determinant positivity
transfer for a supplied Grassmannian affine-point comparison. It does not
construct that geometric comparison.

`IdentityJet.stabilizedModule G n p C` is the genuine categorical biproduct
of the actual identity-jet module of `G` at order `n` and the actual pullback
of the base module sheaf `C` along `p`. If `G` is smooth and affine and `C`
has finite local bases, then `stabilizedModule_hasFiniteLocalBasis` constructs
finite local bases of this actual sheaf. The construction uses the proved
actual jet bases, pullback and genuine biproduct frames.

`lieDeterminantDual_isAmple_of_stabilizedGrassmannian` assumes that the base
of `G` is compact and quasi-separated, that the target of `p` is affine,
and that `n` is positive. Supply an affine morphism to the existing quotient
Grassmannian `D.Gr`, a prescribed global generator family in the actual
stabilized sheaf, and `HasAffinePointComparison` for that actual sheaf.
This last premise identifies every affine section module with the
classified quotient and preserves its prescribed generators.

The theorem proves ampleness of the dual of the existing actual smooth Lie
determinant of `G`. First, actual frames derived directly from the quotient
comparison give ampleness of the existing chosen determinant of the
stabilized actual sheaf. The actual biproduct determinant factorization
identifies this line with the actual jet determinant tensored with the
actual pullback of the base determinant. Affine-base twist ampleness removes
that factor. The completed positive-order actual jet-to-Lie theorem then
proves ampleness of the actual Lie determinant dual. No global constant
rank, additional frame cover, base-line triviality or jet-base-change
premise is retained.

The provenance is internal: this is the composition of the already proved
actual free-frame, chosen determinant, biproduct, base pullback, ampleness
locality and jet-to-Lie results. For a parabolic application the actual
affine classification morphism, its exact affine-point comparison, the
finite-basis base complement and a positive order must still be supplied.
This module by itself does not prove the finite-parabolic target.
