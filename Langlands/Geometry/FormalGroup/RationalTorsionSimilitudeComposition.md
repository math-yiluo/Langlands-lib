# Restriction and composition of local rational torsion similitudes

`HasLocalTorsionSimilitude.restrict` preserves the same multiplier
on an open subset. Intersect each witnessing open with the subset
and extend its integral numerator along the structure-section map.
The comparison between the two coefficient extensions is an
isometry of the actual torsion polarizations. The restricted
numerator therefore satisfies the same integral pairing equation.

`HasLocalTorsionSimilitude.comp` composes the two integral numerators
on the intersection of their witnessing opens and adds their
denominator exponents. The finite-kernel composition theorem
supplies the isogeny condition for the composite. If the original
rational multipliers are \(c,d\) and the exponents are \(n,m\), the
integral multipliers multiply to \(p^{2(n+m)}cd\). Section
composition and scalar multiplication give the required
denominator-cleared identity for the composite.

The construction applies to the rational multiplier relation used
for the polarized framing in Harris (1997), Appendix, printed
p. 113 (PDF p. 39). It works with the existing general scalar and
fraction-field parameters of that relation, including the
\(\mathbf Z_p,\mathbf Q_p\) specialization.
