# Finite group-algebra coefficients from natural Lie coordinates

This internal helper replaces finite-type assumptions in coefficient extraction
by the supplied natural finite coordinates. Every Lie vector over a group
algebra expands in the constant coordinate vectors. Applying the existing
individual coefficient maps shows that its coefficient support is contained
in the finite union of the supports of its coordinate entries. The resulting
finite coefficient family reconstructs the original vector by the existing
coefficient extensionality and monomial formulas.

These are derived linear algebra facts about the published actual Lie kernel
and `Lie.FiniteCoordinates`, with no additional structural assumptions on the
group scheme.
