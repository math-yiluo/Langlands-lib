# Uniform annihilators of the original orbit constant terms

This derived module completes the algebraic realization of uniform split
annihilators for the original orbit constant terms. Its one remaining spectral
hypothesis is explicitly named `HasStandardUnitaryJacquetContraction`: at the
specified actual component point, every nonunitary generalized exponent of
the original unitary induced Jacquet family has norm strictly below one.
The module does not prove this analytic hypothesis.

Literal twists of the original inducing representation cover the full
discrete-series unitary orbit. Choose one such twist at each orbit class;
no continuity of this auxiliary choice is asserted or needed. The original
orbit coefficient is its representative coefficient. The published equality
of the original induced coefficient-map range with the normalized tensor
coefficient-map range realizes it as a coefficient tensor of that same twist.
The chosen standard constant terms agree exactly.

The original smooth orbit section supplies one common compact-open group of
bi-invariance. Refine it by a member of the original standard normal basis.
Its compactness and standard parabolic clauses hold, and right invariance
passes to every actual chosen constant term. Apply the standard fixed-level
annihilator reduction to the chosen tensor family, indexed by the entire
original orbit. The fixed dimensions, nilpotence orders, exponent counts,
common root gap and polynomial degrees are derived. The result is the existing
`HasUniformSplitAnnihilators` of the original chosen constant terms, hence of
their existing weak and positive parts.

The target's source action, literal subgroups, rational norm family, original
central quotient and actual orbit remain unchanged. Field and representation
carrier universes are independent. This conditional intermediate result does
not complete positive decay or introduce an additional hypothesis into that
published target.

The contextual original source is Waldspurger, *La formule de Plancherel pour
les groupes p-adiques, d'après Harish-Chandra* (2003), VI.2.1 and VI.2.3,
printed pp.297–300, source `waldspurger-2003-plancherel`. The implemented
proof combines the actual full-orbit coefficient and common-invariance
theorems with the exact standard-family spectral and fixed-level adapters.
