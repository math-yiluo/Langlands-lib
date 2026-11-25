# Differentiating actual symmetric-power matrices

For an arbitrary matrix over a commutative ring,
`SymmetricDifferential.derivation N` is the derivation of the genuine
multivariate polynomial algebra sending generator `X j` to
`sum_i C (N i j) * X i`. `SymmetricDifferential.matrix N d` is the matrix
of its degree-`d` action in the canonical monomial coordinates. These
algebraic helpers require no characteristic or reducedness assumption.

To identify this with the actual infinitesimal action, `dualPolynomialMap`
interchanges polynomial variables with dual-number coefficients. It sends
a constant dual number `(a,b)` to `(C a,C b)` and each polynomial variable
to its constant dual-number inclusion. Induction on multivariate polynomials
proves that taking a polynomial coefficient commutes with taking the epsilon
coefficient. The multiplication-by-variable step uses the exact monomial
coefficient formula.

`derivationLift D` records `(P,D P)` as an algebra homomorphism into the
dual numbers of the polynomial algebra. For `infinitesimalMatrix N`, whose
entries have identity constant term and epsilon term `N`, its symmetric
substitution followed by `dualPolynomialMap` equals that derivation lift.
The proof checks constants and generators and uses multiplicativity and
additivity. Reading coefficients identifies the differential matrix entries
with coefficients of the genuine derivation. Expanding an arbitrary
homogeneous polynomial in its finite monomial basis gives
`SymmetricDifferential.matrix_mulVec`, the action formula on all homogeneous
coordinate vectors.

For an actual representation over a field,
`symmetricPower_tangentMatrix` proves that the tangent matrix of the actual
symmetric-power representation is exactly this derivation matrix evaluated
at the original tangent matrix. The original representation's actual
dual-number point is `I + epsilon * tangentMatrix`, by its published tangent
kernel coordinates. The all-test symmetric-power formula computes its image;
extracting epsilon coefficients gives the claimed equality. No affineness,
finite-type, smoothness or reducedness assumption on the group is used.

This is an internal coordinate implementation of the source's statement
that the induced Lie action on the symmetric algebra is by derivations.
It retains actual dual-number scheme points and does not replace them by
rational-point data. No nilpotent exclusion or classification theorem is
asserted by this module.

Source: M. Demazure and P. Gabriel, *Groupes algebriques*, Tome I (1970), IV, section 3, proof of Theorem 3.6, printed p.510 (PDF p.540). Registered source `provided-fbc22c29e33197d3b9f2e242cdac44714e2e1a2f5faa337e9ebc1d657ad1d6fe`, SHA-256 `fbb2f907cc281afba245917449bae4bca1175c35215539c700575c517069e127`.
