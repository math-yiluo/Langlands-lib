# Uniform backward recovery for the original unitary constant terms

This derived supporting module applies the positive-annulus recurrence bound
to the original standard normalized induction and its chosen full standard
constant term, across every unitary unramified twist of the original
irreducible admissible source.

`HasStandardUnitaryJacquetExponentAnnulus` specifies one positive annulus at
the chosen component point for the generalized Jacquet exponents of all the
unitary fibers. Character values are units, so their norms are positive.
Inserting one into the positive part of the finite set of such norms gives
positive minimum and finite maximum with `0 < η ≤ 1 ≤ Λ`. The finite-set
theorem applies to the fixed irreducible admissible source.

At a common standard compact open level, the original untwisted induced fixed
dimension bounds each fiber's Jacquet fixed dimension. Right invariance of the
chosen constant term puts its source vectors in this fixed space. Every label
occurring in the resulting finite-dimensional decomposition defines a genuine
generalized eigencharacter of the same actual Jacquet action, so the uniform
annulus applies. The unpadded full annihilator and inverse-polynomial estimate
then bound each constant-term value in norm by `D^r` times the sum of the
norms of the values beginning at the `r`th forward component translate.
The positive constant `D` depends only
on the source, level and component point, and the finite sum has length
`r*d*d+1`, where `d` is the untwisted induced fixed dimension. It is independent
of the twist and coefficient tensor.

The contextual original source is Waldspurger, *La formule de Plancherel pour
les groupes p-adiques, d'après Harish-Chandra* (2003), VI.2.1 and VI.2.3,
printed pp.297–300, source `waldspurger-2003-plancherel`. The quantitative
positive-annulus recovery is derived project content. This result supplies
neither a bound for the later segment nor the principal positive-part decay.
