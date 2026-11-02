# Equal-rank gamma continuation for the two-block lower induction

This internal composition proves `equalTwoBlockSymmetricGammaProduct_at_zero`:
for full Whittaker-type representations `π` of rank `t + 1` and the two ordered
blocks `σ i` whose ranks sum to `t + 1`, complete symmetric gamma certificates
exist for both block pairs and their product is a complete symmetric gamma
certificate for the actual ordinary lower induced representation
`TwoBlockJacquet.inducedRep F h σ`. The supplied self-dual Haar measure is retained.
The field and the two carrier universes remain independent. Reducible full
Whittaker-type representations are allowed.

`EqualOppositeRealRayGammaCertificates` records complete gamma certificates for
the opposite complex twists on a sufficiently large real ray, with fixed original
block factors and their literal spectral rescalings.
`exists_equalOppositeRealRayGammaCertificates` obtains this assertion from
`exists_equalTwoBlockSymmetricGammaProduct`, the proved unramified gamma
transport and uniqueness of complete certificates. It uses the actual ordered
opposite-twist induction.

`equalTwoBlock_gamma_at_zero` works with an arbitrary compatible quotient measure
that is finite on compact sets, nonzero original functionals, actual model
coefficients, a specified Fourier pair, an original model minus-one scalar,
fixed nonzero clearing polynomials, and real-ray clearing and gamma certificates.
The actual opposite Whittaker family extends the specified second coefficient at
zero. Its central right translate and its actual second dual have entire
literal determinant-slice coefficients, by `equalGammaSliceFamilies_entire`.
Full Whittaker type supplies rational continuations and absolute bilateral
expansions at every complex parameter for both families.

On the real ray, a complete gamma certificate supplies the current model scalar
and functional equation. The fixed central translate multiplies the primal
integral by that scalar to the power `t`. Rational continuation uniqueness and
`gammaFunctionalEquation_absorb_scalar` therefore produce an equation with scalar
one. The same translated coefficient is covered by real-ray clearing. Applying
`gammaFE_oppositeSpectralProduct_at_zero` continues these actual equations to
zero. The original model scalar and the integral translation identity then
restore the required equation for the original primal and dual integrals. No
constancy of the parameter-dependent model scalars is asserted.

The final wrapper `equalTwoBlockSymmetricGammaProduct_at_zero` chooses the
canonical compatible quotient Haar measure, nonzero functionals, complete
original block gamma certificates and block L polynomials internally. The
polynomials have nonzero product since both constant coefficients are one.
It combines the separately obtained clearing and gamma rays beyond their maximum
bound. An independently constructed complete induced gamma certificate supplies
a Fourier pair and an actual nonzero rational zeta value. The preceding
continuation theorem applies to this value. Uniqueness of rational continuations
identifies its primal and dual continuations with those of the complete
certificate. `GammaFunctionalEquation.gamma_unique` then identifies the complete
induced gamma factor with the product of the two fixed block factors, transferring
the entire certificate, including all measure and functional quantifiers and
existence witnesses.

This file is derived from the imported actual-family, real-ray, unramified
transport and rational-comparison results; it introduces no new translation from
literature. The actual lower-to-upper reversal and retained integral comparisons
are dependencies of the real-ray result. This unit proves the equal-rank lower
induction boundary. It does not yet transport the result to the upper normalized
induction in the closed task targets, nor prove the strictly dominant range.
