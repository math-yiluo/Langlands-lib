# Boundary cancellation and reflected defect rigidity

`Langlands.RankinSelberg.BoundaryDefectRigidityStatement` is a closed
proposition definition. It states an internal algebraic lemma and does not
prove it.

## Exact statement

For all real numbers \(a,b\), complex units \(\delta,c\), integers \(m\), and
complex polynomials
\[
  A,\ C,\ P,\ D,\ A^\vee,\ C^\vee,\ P^\vee,\ E\in\mathbf C[X],
\]
written in Lean as `A`, `C`, `P`, `D`, `Adual`, `Cdual`, `Pdual` and `E`,
assume:

- \(0<a\), \(0<b\), and \(|\delta|<ab\).
- \(A(0)=C(0)=P(0)=1\) and \(A^\vee(0)=C^\vee(0)=P^\vee(0)=1\). In Lean these
  six normalizations are `A.coeff 0 = 1`, …, `Pdual.coeff 0 = 1`.
- The two product identities
  \[
    A\,C=D\,P,\qquad A^\vee C^\vee=E\,P^\vee
  \]
  hold in \(\mathbf C[X]\).
- The two divisibilities \(A\mid P\) and \(A^\vee\mid P^\vee\) hold in
  \(\mathbf C[X]\).
- \(C(z)\ne0\) for every complex \(z\) with \(|z|<a\), and \(C^\vee(z)\ne0\)
  for every complex \(z\) with \(|z|<b\).
- The following equality holds in the rational-function field
  \(\mathbf C(X)\):
  \[
    \iota(D)=
      \bigl(\operatorname{RatFunc.C}(c)\,X^m\bigr)\,
      \operatorname{subst}_{\delta}(\iota(E)).
  \]

The conclusion is the conjunction
\[
  D=1,\qquad E=1,\qquad P=A\,C,\qquad P^\vee=A^\vee C^\vee
\]
of equalities of polynomials.

Here \(\iota\) is `algebraMap (Polynomial ℂ) (RatFunc ℂ)`, the actual
embedding of polynomials into rational functions. The reflection is the
existing `Langlands.LocalFactor.RationalReflection.subst δ` from
`Langlands.LocalFactor.WeilDelignePair`, the actual \(\mathbf C\)-algebra
homomorphism of \(\mathbf C(X)\) substituting \(X\mapsto\delta/X\). The scalar
\(c\) is embedded by `RatFunc.C`, and \(X^m\) is an integer power of
`RatFunc.X`. The rational identity is an equality of field elements, not a
pointwise identity on an unspecified domain.

## Scope of the hypotheses

- The two defects \(D\) and \(E\) carry no hypothesis of their own except the
  displayed product identities and the reflection identity. They are not
  assumed to be normalized, to be units, to have no complex roots, to avoid
  roots in a disk, or to divide \(C\) or \(C^\vee\). Their divisibility of the
  boundary polynomials \(C\), \(C^\vee\), their root exclusions and the
  normalizations \(D(0)=E(0)=1\) are consequences that a proof must derive.
- The root exclusions concern only the open disks of radii \(a\) and \(b\);
  roots on the boundary circles are allowed. No polynomial is assumed to have
  no complex roots at all.
- Both radii are arbitrary positive reals, related only by the strict gap
  \(|\delta|<ab\). The scale \(c\) and the reflection parameter \(\delta\) are
  arbitrary nonzero complex numbers, represented as units; in particular \(c\)
  is not restricted to a positive real number. The exponent \(m\) is an
  arbitrary integer, so the monomial may have a pole at zero.

## Prospective proof

The following describes a proof plan, not an implemented proof.

1. Write \(P=A\,S\) using \(A\mid P\). Since \(A(0)=1\), the polynomial \(A\)
   is nonzero, so cancelling \(A\) in \(A\,C=D\,A\,S\) gives \(C=D\,S\).
   Hence \(D\mid C\). Dually, \(P^\vee=A^\vee S^\vee\) and
   \(C^\vee=E\,S^\vee\), so \(E\mid C^\vee\).
2. Evaluating \(C=D\,S\) shows that a root \(z\) of \(D\) with \(|z|<a\) would
   be a root of \(C\). Thus \(D(z)\ne0\) for \(|z|<a\), and similarly
   \(E(z)\ne0\) for \(|z|<b\).
3. Comparing constant coefficients, \(A(0)C(0)=D(0)P(0)\) gives \(D(0)=1\).
   Likewise \(E(0)=1\).
4. The Library theorem `Langlands.RankinSelberg.reflectionRigidity`, which
   proves `Langlands.RankinSelberg.ReflectionRigidityStatement` in module
   `Langlands.Representation.RankinSelberg.ReflectionRigidityProof`, applies
   with the same \(a,b,\delta,c,m\) to \(D\) and \(E\). It gives \(D=1\) and
   \(E=1\).
5. Substituting \(D=1\) and \(E=1\) into the product identities gives
   \(P=A\,C\) and \(P^\vee=A^\vee C^\vee\).

This statement module imports only `Langlands.LocalFactor.WeilDelignePair`,
which provides the reflection. A proof following this plan would also import
the published reflection-rigidity proof module rather than repeating its
evaluation and root-separation argument.

## Provenance and consumer obligations

This is an internal algebraic abstraction, not a verbatim theorem of the
literature. The cancellation in steps 1–3 is elementary and internal. The
motivating application is H. Jacquet, I. I. Piatetski-Shapiro and
J. A. Shalika, *Rankin-Selberg Convolutions*, American Journal of
Mathematics 105 (1983), §9.4, printed pp. 461–462 (PDF pages 96–97,
one-based), registered as `jpss-1983-rankin-selberg` with SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`. The cited
pages were read directly.

There, display (19) writes \(L(s,\xi\times\eta)\) as a polynomial correction
\(P(q^s,q^{-s})\) times the product of the factors \(L(s,\pi_i\times\sigma_j)\),
display (20) is the analogous identity for \(L(1-s,\xi^\iota\times\eta^\iota)\)
with a correction \(\tilde P\), and display (21) equates, within a unit factor,
the quotient \(L(1-s,\xi^\iota\times\eta^\iota)/L(s,\xi\times\eta)\) with the
product of the quotients
\(L(1-s,\tilde\pi_i\times\tilde\sigma_j)/L(s,\pi_i\times\sigma_j)\); the text
then concludes \(P=\tilde P\) up to a unit.
Display (22), deduced from (17) and (19), states that the correction (printed
there as \(P(q^{-s},q^s)\)) times \(Q_2(q^{-s},q^s)\) times the product of the
first-column factors \(L(s,\pi_i\times\sigma_1)\) equals \(1\). Display (23),
deduced from (18) and (20), is the same with \(\tilde Q_1\) and the last-row
factors \(L(1-s,\tilde\pi_m\times\tilde\sigma_j)\). On p. 462, if \(P\) is not
identically one, some \(L(s,\pi_i\times\sigma_1)\) and
\(L(1-s,\tilde\pi_m\times\tilde\sigma_j)\) have a common pole; the bounds of
(8.4) then give contradictory real-part inequalities, so \(P\) is a unit. The present proposition isolates
one algebraic form of this deduction: a divisibility by a known tail divisor
turns a product identity into a divisibility of a boundary polynomial, which
transfers that polynomial's root exclusion to the defect, and reflection
rigidity then removes both defects. The letters here are internal names. In
particular, \(P\) here is not the correction \(P(q^s,q^{-s})\) of display
(19), and no particular translation of the JPSS displays into these
hypotheses is asserted.

A consumer must separately establish every displayed polynomial identity, both
tail divisibilities, all six constant-coefficient normalizations, both
boundary root exclusions, the positive radii, the strict gap and the rational
reflection identity. None of those analytic or representation-theoretic
inputs is hidden in a definition here. This statement has no local field,
representation, L-polynomial existence, gamma-multiplicativity, analytic pole
bound or classification hypothesis or conclusion.
