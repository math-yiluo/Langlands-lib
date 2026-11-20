# The scalar component of the Weil generator

For a rational torsion similitude certificate of multiplier \(c\),
`inverseMultiplierOrder` is the additive order of \(c^{-1}\) in
\(\mathbb Q_p\), with multiplication as the operation on the integer
target used by the component group. The proof compares the canonical
local-field valuation with the \(p\)-adic valuation through their common
valuative relation. Its surjectivity and the fact that \(p\) has the
largest value strictly below one give \(\operatorname{ord}_p(p)=1\).
Thus the multiplier of \(m\)-fold relative Frobenius, \(p^m\), has
order \(m\).

On an affine representative of (A.4), inverse relative Frobenius
replaces the certificate \(c\) by \(p^{-m}c\).
`splitSpecialWeilFrobeniusPoint_exists_multiplierOrder` verifies this
certificate on the actual twisted rigidifier and computes the new
inverse multiplier order as \(\operatorname{ord}_p(c^{-1})+m\).

In the quotient coordinates of (A.2), the second coordinate of a
split similitude is the order of its multiplier. If the rigidifier
has the reciprocal of that multiplier as its certificate, its inverse
multiplier order is exactly this second coordinate. The theorem
`inverseMultiplierOrder_eq_weilComponent_snd` identifies the updated
order with the second coordinate of right translation by
\((\Pi,p^m\Pi^{-1})\). For the residue Frobenius over \(F\), \(m\) is the
residue degree \(f\) in (A.3). These identities compare the scalar
coordinates for the specified certificates.

- Michael Harris, *Supercuspidal representations in the cohomology of
  Drinfel'd upper half spaces*, Invent. Math. 129 (1997), Appendix,
  (A.2)–(A.4), printed p. 114 (PDF p. 40).
- Michael Rapoport and Thomas Zink, *Period Spaces for p-divisible
  Groups*, Annals of Mathematics Studies 141 (1996), Lemma 6.44 and
  proof, printed pp. 309–310 (PDF pp. 321–322).
