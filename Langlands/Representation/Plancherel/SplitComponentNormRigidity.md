# Rational-character norms and the split component

This internal construction supports the faithfulness step used in Renard V.3.5
and in the proof of VI.8.5. It isolates the norm-detection argument from the
separate structural identification of an actual Levi with the centralizer of
its split component. The latter identification is not asserted here.

Let \(k\) be any nonarchimedean local field, \(M\) a connected reductive group
scheme over \(k\), and \(a:A\to M\) an actual split component.
For an automorphism \(\phi:M\to M\), `automorphismRestriction` constructs an
endomorphism \(f:A\to A\) satisfying \(f\mathbin{\gg}a=a\mathbin{\gg}\phi\).
Central split-torus factorization provides this construction for any affine
ambient group, before reductivity or norm preservation is used.

If
\[
  |\chi(\phi(x))|=|\chi(x)|
\]
for every central rational point \(x\in Z(M(k))\) and every rational algebraic
character \(\chi\) of \(M\), the implemented theorems prove \(f=\mathrm{id}_A\)
and \(a\mathbin{\gg}\phi=a\). The norms are the actual residue-normalized field
norms of `Plancherel.rationalNormCharacters`, not a supplied character family.
The conclusion is equality of scheme morphisms, with no splitness assumption
on \(M\), no characteristic restriction and no choice of torus coordinates.

The proof first derives equality of integer orders from equality of
norms by applying their published equal-kernel law to a quotient of field
units. On the split torus, evaluation of cocharacters at the fixed uniformizer
identifies these orders with the integral character–cocharacter pairing. Its
perfectness shows that two characters with equal norms on all rational points
are equal. Applying this to the restrictions of rational characters of \(M\)
shows that \(f\) fixes the image of \(X^*(M)_k\) in \(X^*(A)\).

That image has finite index by the published finite-index character-restriction
theorem for split components of connected reductive groups. Multiplication
by its nonzero index carries every character into the image. Pairing with
each cocharacter and cancelling that nonzero integer extends the equality to
every character of \(A\). Characters of a split torus separate morphisms into
it, so \(f\) is the identity.

The construction and argument are derived internal content. Their mathematical
role is the norm-coordinate implication behind Renard's faithful Weyl action:
Renard, *Représentations des groupes réductifs p-adiques*, 9 July 2026 edition,
V.3.5 (printed pp.110–111 / PDF pp.116–117) and V.3.19 (printed p.115 /
PDF p.121), used in VI.8.5. This module proves neither the Levi-centralizer
identification nor generic irreducibility.
