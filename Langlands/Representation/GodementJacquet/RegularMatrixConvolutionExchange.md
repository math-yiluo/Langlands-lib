# Convolution exchange for regular matrix tests

This internal helper derives actual Hecke convolution and operator cross
identities from determinant-density cancellation and square Fourier exchange.
It supplies an intermediate analytic identity, without constructing a scalar
gamma factor or asserting the full supercuspidal functional equation.

Fix a p-adic field `F`, its canonical topology and residue-normalized absolute
value, a positive size `d=n+1`, and the canonical measure
`mu = generalLinearHaar F.Carrier n`. Write `iota(g)=(g^-1).transpose` and
`w_s(g)=|det(g)|_F^s`, with the existing complex-power convention. The definition
`dualWeightedRegularMatrixTest F s` sends a regular full-matrix test `Xi` to the
actual group Schwartz–Bruhat test

```text
g |-> Xi(iota(g)) w_(s-d)(g).
```

Its construction is the homeomorphism pullback of
`weightedRegularMatrixTest F (d-s) Xi`. Compact support and local constancy
therefore come from those of the existing weighted regular test.

The lemmas `dualWeightedRegularMatrixTest_convolution_left` and
`dualWeightedRegularMatrixTest_convolution_right` compute the actual left-Haar
convolution, with convention `(f*g)(k)=integral f(g)g_test(g^-1*k) dmu(g)`.
For arbitrary regular tests `Xi` and `Psi`, the first computation is

```text
(dual_s(Xi) * weighted_s(Psi))(k)
  = w_s(k) integral Xi(g) Psi(g.transpose*k) w_d(g) dmu(g).
```

For arbitrary regular tests `Phi` and `Xi`, the second is

```text
(weighted_s(Phi) * dual_s(Xi))(k)
  = w_(s-d)(k) integral Phi(g) Xi(g.transpose*iota(k)) w_d(g) dmu(g).
```

Matrix functions in these displays are evaluated on the underlying matrices.
The first equality substitutes the measure-preserving inverse transpose; the
second expands its group homomorphism law. The determinant weights combine by
addition of their complex exponents. `determinantWeight_inv_inverseTranspose`
records the unchanged determinant of `(iota(g))^-1`, while
`determinantWeight_neg_dimension` identifies the Fourier Jacobian
`|det(k)|_F^(-d)` with the negative dimension weight.

Now supply a unitary additive character `psi`, a scalar additive Haar measure
`nu`, and its self-duality proof `hsd`. Let `Phi` and `Psi` belong to
`fourierRegularMatrixTests d psi nu hsd`: both the original test and its actual
plus Fourier transform vanish on singular matrices. The theorem
`dualWeightedRegularMatrixTest_convolution_cross` proves

```text
dual_s(PhiHat) * weighted_s(Psi)
  = weighted_s(Phi) * dual_s(PsiHat).
```

Its proof applies `exists_integral_regularMatrix_density` to the two displayed
kernels. The left kernel vanishes on singular matrices because `PhiHat` does;
the right does because `Phi` does. The same positive Haar-normalization scalar
occurs on both sides and cancels. The remaining additive matrix integrals are
exactly `padicSquareFourierIntegral_crossExchange`, for the literal square
product of `nu`. Its determinant Jacobian combines with `w_s(k)` to give
`w_(s-d)(k)`. No determinant-one restriction is imposed on `k`.

Finally, let `rho` act on an arbitrary complex module `V`, with smoothness
proofs for `rho` and for `rho.comp iota`. The theorem
`regularMatrixZetaOperator_inverseTranspose` identifies the actual zeta
operator for `rho.comp iota` at `d-s` with the integrated `rho` action of
`dualWeightedRegularMatrixTest F s`. It uses the published change of variables
for integrated actions and the canonical inverse-transpose Haar invariance.
Then `regularMatrixZetaOperator_inverseTranspose_cross` applies
`integratedAction_convolution` to obtain, for every complex `s`,

```text
D_s(Phi) A_s(Psi) = A_s(Phi) D_s(Psi),
A_s(Phi) = regularMatrixZetaOperator F rho hRho s Phi,
D_s(Phi) = regularMatrixZetaOperator F (rho.comp iota) hIota (d-s) PhiHat.
```

Products here are endomorphism composition. The carrier needs no topology or
completeness, and neither admissibility nor supercuspidality is assumed. The
field and representation carrier have independent universes. The provenance is
internal: all steps specialize the existing concrete tests, Fourier transform,
Haar-density formula and integrated-action laws; no unproved functional
equation or scalar comparison is a premise.
