# Compact weighted bounds for the actual full orbit constant terms

`HasRationalOrbitConstantTermCompactBounds` carries the uniform weighted
bound for the chosen full constant terms of a smooth induced orbit section.
For every compact subset of the target Levi there is a positive constant
that bounds their norms by the constant times the original Levi Xi on that
subset, uniformly over the orbit. The theorem derives the property from the
original structural data.

The generic first lemma applies to any group-function family with a common
open subgroup of right invariance and a uniform bound at each fixed group
point. Cover a compact set by the open sets `m*U`. A finite subcover reduces
the family values to finitely many fixed-point bounds. The reciprocal of an
everywhere positive continuous weight is bounded on that compact set, giving
the stated positive weighted constant. No topology on the parameter set is
needed.

For the actual orbit family, the previously constructed recurrence argument
supplies its fixed-point bounds, while its common right-invariance subgroup
is inherited from the original orbit coefficient section. Continuity and
strict positivity of the original actual Levi Xi finish the application.
The full unitary orbit and every original standard index are retained.

The contextual source is Waldspurger, *La formule de Plancherel pour les
groupes p-adiques, d'après Harish-Chandra* (2003), VI.2.3, printed pp.299–300,
source `waldspurger-2003-plancherel`. The finite-cover argument and the
recurrence route to full constant-term boundedness are derived project
content. This proves the compact-bound input to positive-part decay; it does
not prove the remaining global growth or spectral contraction inputs.
