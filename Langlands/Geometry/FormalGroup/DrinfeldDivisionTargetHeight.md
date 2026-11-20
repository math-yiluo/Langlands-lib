# Signed kernel-rank height of the division twist on the reduced target

Drinfel'd, *Coverings of p-adic symmetric regions* (1976), §2 A,
printed p. 109 (PDF p. 3), uses the inverse division unit in the
framing and replaces the action of an order element \(a\) on \(Y\)
by the old action of \(g^{-1}ag\). The reduced-norm order term in
that formula is normalized by the field valuation. Harris,
*Supercuspidal representations in the cohomology of Drinfel'd upper
half spaces* (1997), Appendix, printed p. 112 (PDF p. 38), defines
height as a difference of base-\(p\) logarithms after clearing a
power of the rational prime \(p\). Here the formal \(O\)-module height
uses the uniformizer and the residue cardinality \(q\).

For a `DrinfeldFramedAtlas`, the whole full-order framing \(\rho\)
intertwines the actual rational actions of the division algebra.
Composing with its actual inverse shows that the action of \(g^{-1}\)
on the reduced target is \(\rho\circ g^{-1}\circ\rho^{-1}\), where
the middle map uses the original extended frame on the same cover.
Both endpoints have scalar height \(d^2\). The inverse of the
height-zero framing has height zero by the kernel-rank calculation
for inverses, and composition adds the three actual heights. Thus
on every test of the original reduced cover the forward twist has
height \(-d\,\operatorname{ord}_K(\operatorname{Nrd}(g))\).
`reducedTargetDivisionWithHeight` returns the original twist
quasi-isogeny with this certificate.
