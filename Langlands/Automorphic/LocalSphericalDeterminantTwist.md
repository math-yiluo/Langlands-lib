# Actual spherical fixed spaces under determinant multiplication

For a number field in an arbitrary universe, a finite place, a positive
rank, an actual local automorphic realization, and a finite-order Hecke
character, this internal construction assumes that the actual local
determinant character is trivial on the actual integral matrix subgroup.

`determinantTwistSphericalEquiv` restricts actual determinant multiplication
to a complex-linear equivalence between the existing spherical fixed
submodules of the original and actual multiplied realization. It first
uses the published equality of fixed spaces for a scalar twist whose
character is trivial on the subgroup, then restricts the existing genuine
equivariant multiplier comparison. The published completion/p-adic integral
subgroup equality identifies the subgroups. Its underlying map is actual
determinant multiplication.

`standardHeckeOperator_determinantTwist` compares the existing standard
double-coset operators under this equivalence. The operator on the
multiplied space is the transported original operator times the actual
local determinant character at the existing standard diagonal. The sign
is positive, in agreement with the published positive right-translation
action. Both operators use the existing spherical Haar measure of subgroup
mass one and the existing standard diagonal normalization.

The proof uses the published finite-sum formula for these genuine
double-coset operators. Every labelled coset representative lies in the
standard diagonal double coset. Multiplicativity and the assumed integral
triviality make its character value equal to the diagonal character value.
The published scalar covariance of actual determinant multiplication,
linearity, and the finite sum then prove the operator identity.
`standardHeckeOperator_determinantTwist_eigen` transports each supplied
scalar eigen-equation with that same multiplier.

Provenance is internal composition of the published actual local image,
fixed-vector, p-adic subgroup comparison, standard Hecke finite-sum, and
multiplier covariance constructions. No irreducibility, admissibility,
nonzero occurrence or spectral-existence premise is introduced. The local
character-triviality premise is explicit; this file chooses no exceptional
set. It does not identify the multiplier with a uniformizer power, scale
Satake parameters, classify spherical representations or assert weak
global association.
