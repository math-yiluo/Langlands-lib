# Topology and basic inclusions of facet radical preimages

Worker 302 supplies a derived helper module for the proof of corrected
Kaletha–Prasad Proposition 13.5.2. It uses the published
`facetPositiveSubgroup` and `facetZeroFixer` without changing their definitions.
All declarations work at an arbitrary universe `u` and use the canonical point
topology on `G(F)`.

The definition `facetPositiveOpenSubgroup D Fa` bundles the radical preimage
as an `OpenSubgroup`. Openness and compactness are direct applications of
`SpecialFibreQuotientData.localField_isOpen_positivePoints` and
`.localField_isCompact_positivePoints` in `IntegralModels.DepthZeroCompactOpen`.
These conclusions need local finite type of the generic group; they do not
need availability or validity of the supplied building datum. The module also
records compactness of the subgroup as a space. Total disconnectedness follows
by restricting the point topology of the affine group, using
`rationalPoint_totallyDisconnectedSpace_of_localField`.

Under `D.SatisfiesGroupAxioms`, Axiom 4.1.20 identifies neutral integral points
with `facetZeroFixer D Fa`. The published inclusion of the radical preimage in
neutral integral points therefore places it in this fixer and in
`D.base.zeroSubgroup`. The fppf quotient clause of Axiom 4.1.22 identifies its
restriction to the neutral integral-point group with the kernel of parahoric
reduction, so it is normal in the zero fixer. Finally, Axiom 4.1.22(7) gives
`facetPositiveSubgroup D Fa ≤ facetPositiveSubgroup D Fb` whenever `Fa ≺ Fb`.
Availability for a single group supplies all these hypotheses through
`IsAvailableFor.groupAxioms`.

These are preliminary structural properties, not a proof of the pro-`p`
property, maximality, classification, or normalizer assertion. No arbitrary
Moy–Prasad filtration is used.

The provenance is internal and derived from the cited Library declarations and
KP Axioms 4.1.20 and 4.1.22 (book printed pp.163–164, PDF pp.194–195), as used
in Proposition 13.5.2 (printed pp.476–477, PDF pp.507–508). The correction on
PDF p.49 of the 1 November 2024 corrections changes the ambient group for
maximality to `G(F)^0`; the inclusion proved here has that ambient group.
