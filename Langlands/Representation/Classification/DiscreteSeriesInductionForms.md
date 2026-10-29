# Positive forms and semisimplicity for discrete-series induction

Worker 388 specializes existing Library constructions in this auxiliary module. The field
universe `uF` and Levi carrier universe `uW` remain independent. Its data
construction `leviDiscreteSeriesForm` chooses an actual invariant positive
Hermitian form on the original carrier of an irreducible representation
of the full product Levi that is square integrable modulo its full center
for the supplied arbitrary Borel Haar measure.

The definition installs the topology, Hausdorff and local compactness
instances of the actual Levi supplied by `T`. Second countability follows
coordinatewise from the general linear factors. `T.leviCompactOpen`
supplies compact-open cofinality. The published
`T.leviCentralQuotientHaar_unimodular B μ` supplies right invariance of the
same given quotient measure. With these hypotheses discharged, the
published `squareIntegrableUnimodularUnitarity` provides the form's
existence, and classical choice selects it. That imported theorem uses a
nonzero smooth functional and the integral of its conjugate-first
coefficient product. No additional form or functional is assumed here.

The generic corollary
`isSemisimple_normalizedParabolicInduced_of_admissible_unitarizable`
applies published normalized-induction unitarity and admissibility to the
same actual representation. The ambient general linear group has
compact-open cofinality. The published `admissibleUnitarySemisimplicity`
therefore proves algebraic complete reducibility of its normalized upper
induction.

`isSemisimple_bothInduced_of_squareIntegrable` applies this corollary to
the chosen form and to admissibility contained in square integrability.
For the opposite induction it uses the published `leviReverse` continuous
group isomorphism. Pulling the original form back along this isomorphism
preserves its inner product and changes its invariance proof by
precomposition. Admissibility is transported by
`isAdmissible_comp_continuousMulEquiv`. The upper corollary applied to the
reversed block shape proves semisimplicity of the reversed upper induction.
The actual `oppositeReversalEquiv` transports this conclusion to the
original opposite induction by the corresponding group-algebra linear
equivalence. Both conclusions concern the original given `σ`; the reversed
representation occurs only in this intermediate construction.

The upper induction uses positive upper half-modulus covariance and the
opposite induction inverse upper half-modulus covariance, both with right
translation. These normalizations are retained by the published reversal
equivalence; no new comparison of actual function spaces is postulated.

This is an internal derived construction from the named published
coefficient-integral, induction, admissibility and reversal results. It
does not use tempered induction preservation, tempered unitarity, a
classification or exhaustion theorem, or the summand criterion. It proves
neither the same-sigma opposite-to-upper embedding comparison nor the
closed summand target. No new original-source assertion is made.
