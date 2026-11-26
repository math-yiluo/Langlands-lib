# The generator component and Clozel regularity

`sigmaRegularCyclicGLComparison` proves that the Library's σ-regular
condition implies regularity in the adjoint-multiplicity sense on the
generator component of the cyclic semidirect product.

At a σ-regular matrix the algebraic multiplicity of \(1\) is \(n\).
For any invertible matrix \(\delta\), join it by an affine line to an
explicit σ-regular point. For a matrix \(g\) on this line, let \(R_g\)
and \(L_g\) be right and left multiplication on the base-field matrix
space. The operator \(R_g\) is invertible when \(g\) is invertible.
The identity
\(L_g\sigma-R_g=R_g(\operatorname{Ad}(g)\sigma-1)\)
shows that the determinant pencil
\(\det(T R_g-(L_g\sigma-R_g))\) is the shifted adjoint characteristic
polynomial times \(\det R_g\). Its coefficients are polynomials in the
line parameter. The coefficients of \(T^k\) for \(k<n\) vanish at
every invertible σ-regular parameter, a cofinite set. They therefore
vanish identically. Evaluating at \(\delta\) and cancelling the
nonzero determinant proves the lower bound \(n\) there.

The resulting minimum on the generator component is \(n\). The theorem
`twistedCharacterFromCyclicGL` combines this comparison with the
semidirect character restriction, giving the full published twisted
integrability proposition from `CyclicGLCharacterRegularityStatement`.
This premise is the analytic character theorem on the cyclic
semidirect models.

Clozel, *Characters of non-connected, reductive p-adic groups*, §2.2,
printed p. 151, defines regularity by the minimum adjoint root
multiplicity on a component. Source ID `clozel-1987-nonconnected-characters`,
SHA-256 `11f4169a65a0716f162928dd4ed87995bb60cb5275cecf7896ee655cec86eb29`.
Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of
the Trace Formula*, Chapter 1, Proposition 2.2, printed pp. 11–12,
uses the comparison for cyclic field extensions. Source ID
`arthur-clozel-1989-base-change`, SHA-256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
The determinant argument applies to arbitrary cyclic algebras over
characteristic-zero fields.
