# Chamberhood of a maximal facet positive subgroup

This internal construction works at arbitrary universe `u`. Assume the
single-group KP axioms for the supplied datum `D`, the facet reductive comparisons,
the finite-field normal-Sylow-torus statement, and the pro-p property of the
positive subgroup of the given facet. If that positive subgroup is maximal among
open pro-p subgroups of `D.base.zeroSubgroup`, then the facet is a chamber.

`maximalPositiveFacetAsChamber` retains the literal input facet and attaches this
chamber certificate. Its value theorem is definitional equality.

The proof reduces the positive subgroup inside the fixer's own actual parahoric
reduction. Maximality gives a Sylow subgroup of the reductive quotient point
group via `facetReductionSylow`. The facet fixer normalizes its positive subgroup,
so this Sylow image is normal. The finite-field input makes the actual reductive
quotient a torus. The first facet comparison then identifies the original facet
as a chamber. This route needs no boundedness premise for a normalizer.

The provenance is internal composition of the published actual-reduction Sylow
construction, normality transport and chamber-torus comparison interface. The
finite-field theorem and comparison remain explicit inputs to this focused
unit. This is not a proof of the full available maximal pro-p proposition and
does not assert the chamber normalizer identity.
