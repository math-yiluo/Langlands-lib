# Conditional comparison for complete-local multiplicative-type extensions

Worker 875. This construction retains two explicit premises:
`MultiplicativeTypeCompleteLocalDeformationStatement` and surjectivity of the
character classification for split diagonalizable Hom sets over the coefficient
ring. Their independently reviewed proofs are not assumed to be published here.

Over a complete local noetherian ring, let the middle affine flat finite-type
group occur in an actual fppf quotient sequence whose kernel representative
and quotient are diagonalizable. Given a specified diagonalization of the
special fibre, `diagonalizingIso` constructs an actual isomorphism from that
same diagonalizable model over the original ring to the middle group.
`diagonalizingIso_special` proves that its pullback homomorphism is exactly
the specified special-fibre homomorphism.

The deformation premise lifts the special-fibre isomorphism to an open and
closed subgroup embedding. Applying the same premise to a map from the
diagonalizable kernel into the model, and its uniqueness part to maps into
the middle group, shows that the subgroup contains the full quotient kernel.

The composite to the quotient is a map of diagonalizable groups. The local
character-classification premise represents it by a homomorphism of their full
character groups. Its special fibre is flat and surjective, which implies
injectivity of that character map over the residue field. The same character
map is therefore flat and surjective over the original coefficient ring.
The generic subgroup comparison then identifies the lifted subgroup with the
entire middle group.

No connectedness or commutativity premise is imposed on the middle group in
this comparison: the given special-fibre diagonalization already supplies the
needed information there. Both character groups may contain torsion. This
conditional construction does not prove either explicit premise or the full
arbitrary-base fpqc-and-extension target.
