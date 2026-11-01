# Actual unramified data after determinant multiplication

Given the existing supplied `UnramifiedData` of a genuine positive-rank
finite tensor presentation and a finite-order Hecke character,
`UnramifiedData.determinantTwist` constructs data of that presentation's
genuine determinant-multiplied image. The new exceptional set is the old data
exceptional set union the already proved finite character-tail bound.
The number-field universe and the local-factor carrier universe are independent.

The local factors are the existing positive scalar twists by the actual local
determinant characters. Their irreducibility follows from the published
scalar-twist theorem; admissibility follows from the open-kernel twist theorem
and the proved actual open kernel. The supplied unordered spectrum is scaled
by the local Hecke character on the existing canonical uniformizer unit,
retaining multiplicities. The new scalar-action evidence first transports
the old actual component's spectrum by actual multiplication, with integral
triviality proved outside the character tail. A genuine representation
equivalence then transfers it to the actual component chosen by the new
global presentation. Invariance of the normalized Hecke spectral relation on
the canonical p-adic objects justifies this last step; equality of embedded
subspaces or of their auxiliary complementary vectors is not required.

`determinantTwist_eigenvalues` exposes the resulting spectrum.
`determinantTwist_powerTrace` multiplies its power trace in degree `k` by
the `k`th power of the actual uniformizer character value.
`determinantTwist_eulerPolynomial` substitutes that character value times the
variable in the old Euler denominator. Both follow from the existing
algebraic spectrum-scaling identities. The mass-one Hecke and positive
square-root residue normalizations are inherited unchanged.

`determinantTwist_spectralSystem` identifies the resulting numerical system
with the pointwise scaled original system restricted to the enlarged finite
exceptional set. The two systems therefore have the same power traces and
Euler denominator polynomials almost everywhere. The final two comparison
biconditionals compare the twisted actual-data system with any supplied
numerical system scaled by the same local character values, allowing a
different rank. They preserve and reflect the corresponding comparison with
the original data. The trace relation retains one finite set uniform in every
positive power. The proofs combine the restriction comparison with the
invertibility of common pointwise scaling.

Provenance is internal composition of the genuine determinant-twisted tensor
presentation, actual component comparison, intrinsic admissibility and
irreducibility transport, and supplied actual spherical-spectrum transport.
An old genuine presentation and old unramified data remain explicit inputs.
This constructs their transported data and does not establish factorization
or spectral existence for an arbitrary automorphic representation, Satake
classification, change-of-uniformizer independence, or global association.
