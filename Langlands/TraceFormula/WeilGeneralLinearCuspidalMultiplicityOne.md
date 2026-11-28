# Cuspidal multiplicity one under Weil restriction of GL_n

`WeilGeneralLinearCuspidalMultiplicityOneStatement` concerns the full almost-everywhere
cuspidal subspace of the positive-central rational quotient of `Res_{L/K} GL_{r+1}`.
For a finite extension of number fields, the central split torus is required to have
injective character restriction of finite-index image. The statement also includes the
parabolic dynamic hypothesis, connected reductivity, and right invariance of the
norm-one Haar measure. Two nonzero closed irreducible invariant subspaces coincide
if a complex-linear isometric equivalence between them intertwines their right actions.

`weilGeneralLinearCuspidalMultiplicityOne` proves this by transport. The comparison
`map_positiveImage` identifies the positive subgroup with that of the upper scalar torus.
The quotient homeomorphism sends the Weil quotient Haar measure to a positive multiple
of the upper quotient Haar measure, by `map_positiveQuotientHaar`. Thus pullback
multiplies the `L²` norm by the square root of this factor. Rescaling `cuspidalEquiv` by
the reciprocal gives an isometric equivalence of the cuspidal spaces. The right-action
comparison `cuspidalEquiv_rightAction` remains valid after rescaling.

Transport the two summands to the upper field and use the restrictions of the isometry
to transport their intertwiner. The submodules remain closed, irreducible and invariant
by `IsIrreducibleClosedSummand.comap_symm_of_intertwining`. The theorem
`generalLinearCuspidalMultiplicityOne` makes their images equal, and the isometry
then gives equality of the original submodules.

This is a consequence of the upper-field `GL_n` multiplicity-one theorem and the
adelic Weil comparison. See `GeneralLinearCuspidalMultiplicityOneProof` for the
formalized multiplicity-one input, from Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), Theorem 11.4.3, and Shalika, *The multiplicity one theorem
for GL_n* (1974), Theorem 5.5.
