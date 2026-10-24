# Polynomial rigidity under reciprocal reflection

`Langlands.RankinSelberg.ReflectionRigidityStatement` is a closed proposition
definition. It states an internal algebraic lemma and does not prove it.

## Exact statement

For every pair of real numbers \(a,b\), complex units \(\delta,c\), integer
\(m\), and polynomials \(D,E\in\mathbf C[X]\), assume:

- \(0<a\), \(0<b\), and \(|\delta|<ab\).
- \(D(0)=1\) and \(E(0)=1\), expressed in Lean as `D.coeff 0 = 1` and
  `E.coeff 0 = 1`.
- \(D(z)\ne0\) for every complex \(z\) with \(|z|<a\).
- \(E(z)\ne0\) for every complex \(z\) with \(|z|<b\).
- The following equality holds in the rational-function field \(\mathbf C(X)\):
  \[
    \iota(D)=
      \bigl(\operatorname{RatFunc.C}(c)\,X^m\bigr)
      \operatorname{subst}_{\delta}(\iota(E)).
  \]

The conclusion is \(D=1\) and \(E=1\) as polynomials.
Here \(\iota\) is `algebraMap (Polynomial ℂ) (RatFunc ℂ)`, and the reflection is
the existing `Langlands.LocalFactor.RationalReflection.subst δ` from
`Langlands.LocalFactor.WeilDelignePair`. It is the actual algebra homomorphism
substituting \(X\mapsto\delta/X\), whose involution is proved by
`RationalReflection.subst_subst`. The scalar \(c\) is embedded by `RatFunc.C`.
The exponent is an arbitrary integer, so the monomial can have a pole at zero.
Both scalar parameters are arbitrary nonzero complex numbers, represented as
units. In particular, the scale is not restricted to a positive real number.

The hypotheses specify open disks; roots on their boundary circles are allowed.
The strict inequality \(|\delta|<ab\) is retained. Neither polynomial is assumed
to be a unit or to have no roots on all of \(\mathbf C\). The rational identity
is an equality of field elements, not a pointwise equality on an unspecified
domain.

## Algebraic motivation and prospective proof

The following describes a proof plan, not an implemented proof.
If \(D\) is nonconstant, the fundamental theorem of algebra gives a complex root
\(z\). Its constant-term normalization implies \(z\ne0\).
All factors on the right of the rational identity are regular at this \(z\):
the Laurent monomial is regular and nonzero away from zero, and a polynomial
evaluated at \(\delta/z\) has no pole there. Evaluating the identity therefore
forces \(E(\delta/z)=0\).

The two root exclusions imply
\[
  a\le |z|,\qquad b\le|\delta/z|.
\]
Since the quantities are positive and \(z\ne0\), these inequalities give
\[
  ab\le |z|\,|\delta/z|=|\delta|,
\]
contrary to the strict radius gap. Thus \(D\) is constant, and \(D(0)=1\)
makes \(D=1\).

For the other polynomial, a nonconstant \(E\) would have a root \(w\ne0\).
Evaluating the original identity at \(z=\delta/w\ne0\), using the reciprocal
involution \(\delta/(\delta/w)=w\), would give \(1=0\).
Hence \(E\) is constant, and \(E(0)=1\) makes \(E=1\).
Equivalently, reflection invertibility gives a symmetric root argument.
The existing `RankinSelberg.RationalEvaluation` module supplies regularity and
evaluation lemmas for reflection and integer powers for a later proof.
No evaluation at zero or at a pole is used in this plan.

## Provenance and consumer obligations

This is an internal algebraic abstraction, not a verbatim theorem of JPSS.
Its motivating application is H. Jacquet, I. I. Piatetski-Shapiro and
J. A. Shalika, *Rankin-Selberg Convolutions*, American Journal of Mathematics
105 (1983), §9.4, printed pp. 459–462 (PDF pages 94–97, one-based).
The registered source is `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The cited original pages were read directly.

In particular, displays (19)–(21) on p. 461 compare the polynomial corrections
up to a Laurent unit. Display (22) yields a divisibility by the first-column
Euler denominators, and display (23) gives its reflected, reversed-dual
last-row counterpart. Together with the pole bounds invoked on p. 462, these
lead to incompatible root regions. The proposition isolates this last
algebraic implication using arbitrary explicit radii and a reciprocal scale.

A later consumer must separately derive the rational identity, the two local
root exclusions, the positive radii and strict gap, and the constant-term
normalizations. None of those analytic or representation-theoretic inputs is
hidden in a definition here. This statement has no local field, representation,
analytic factor-existence, gamma-multiplicativity, Laurent-generator,
induction-geometric, or classification hypothesis or conclusion.
