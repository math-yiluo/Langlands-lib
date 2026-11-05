# All-presentation normalized exponent conditions under conjugation

This internal adapter combines ambient transport of compatible root
presentations with inner-conjugation transport of actual normalized Jacquet
exponents. Its provenance is those constructions and the existing definitions
of the normalized cone condition and normalized-exponent temperedness. It
asserts no new comparison with the source's raw logarithmic convention.

`ParabolicRootPresentation.invCompAmbientIso` transports a presentation along
the inverse ambient isomorphism and cancels the composite in its compatibility
witness. Together with forward transport this gives
`compAmbientIsoEquiv`, an equivalence of the entire presentation types. The
proof checks equality of their underlying data; compatibility is a proposition.
Inverse transport preserves the restricted-root vectors and the full
nonnegative cone by the enumeration-free finite-sum description.

`satisfiesNormalizedExponentConeCondition_comp_innerIso_iff` identifies the
published conditions for `p,l,a` and `p ≫ Int(g),l,a`. In both directions
it transports a presentation witness to retain nonempty coverage. For the
universal tests, it transports each supplied presentation in the opposite
direction, invokes the actual normalized-exponent equivalence, and uses equality
of the cones in the same full real character space. Every radical map,
multiplication isomorphism and character remains quantified, and the maps
`l` and `a` remain fixed. No independence across unrelated presentations is
assumed or proved.

`IsNormalizedExponentTempered.standardRestriction` supplies the forward
implication of the exact standard-reduction statement: admissibility is
extracted, and each standard triple is a triple among the universally tested
actual parabolics. This implication needs no maximality, genericity or
minimality assumption on the torus data because it only restricts the tests.

The representation results retain the canonical rational-point topology, the
published Hausdorff local-field, local-compactness and nonarchimedean-group
hypotheses, arbitrary characteristic, nonsplit groups, and independent group
and representation-carrier universes. The cones include the empty-root case.
The converse standard reduction, in particular fixed-family geometric
completeness, is a separate remaining obligation.
