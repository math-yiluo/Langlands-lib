# Actual finite local frames of finite-projective associated sheaves

For any commutative ring `R` and any finite-projective `R`-module `C`,
`tilde_hasFiniteLocalBasis_of_finite_projective C` proves that the actual
associated module sheaf `tilde C` on `Spec R` has actual finite local
bases. No global constant-rank, freeness, nonempty or noetherian
assumption is made.

The proof transports finite generation and projectivity of `C` to the
actual module of global sections of `tilde C` along the standard
`tilde.isoTop` linear isomorphism. The existing finite-projective affine
module neighbourhood theorem then supplies an actual finite free sheaf
neighbourhood of every point. The standard construction from such free
neighbourhoods gives actual local generators which are both locally free
and finite. The rank can depend on the chosen neighbourhood.

`tildeFiniteProjectiveFrames C` chooses an actual `FiniteLocalFrames`
system from that proved finite-local-basis property. Its actual determinant
and actual pullbacks can therefore be used in the already established
biproduct determinant and affine-base twist comparisons. The provenance
is internal: the result packages the existing finite-projective affine
free-neighbourhood theorem and the actual associated-sheaf global-section
isomorphism. It makes no parabolic, orbit or Grassmannian comparison
assertion.
