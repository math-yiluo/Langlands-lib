# Compact quasi-étale comparison from tuple cones and lift compatibility

This internal reduction assembles the finite tuple-cone constructions into the
published compact quasi-étale global comparison target. Its two geometric
inputs remain explicit: `CompactCompatibleTupleConesStatement ρ` and
`HasCompatibleCompactQuasiEtaleLifts ρ`. They are not consequences established
by this module, and neither is an assumption of the original comparison
statement.

`homAcyclic_of_compactTupleCones` chooses the actual limiting cones, compactness
and local lift witnesses supplied by the tuple-cone proposition for each
compatible cover. Their points serve as compact lifted basis representatives,
with identity comparison isomorphisms. The theorem
`exactAt_of_compactTupleCones` then gives Hom-complex exactness in every
positive degree against the ordinary restriction of an injective quasi-étale
equivariant coefficient. This is `HomAcyclic` for the actual
`compactCompatibleCechSystem` defined using the tuple-cone presentation. The
underlying chain complexes depend only on the covers, so choosing witnesses
inside this proof does not change the system's Hom-exactness assertion.

`analyticQuasiEtaleGlobalComparison_of_compactTupleCones` supplies the ordinary
site's local smallness, module sheafification, enough injectives and
local-bijectivity characterization from the published analytic size and site
theorems, in the full coefficient universe of the original target. The
compatible-cover acyclicity reduction turns the preceding Hom-exactness into
acyclicity of restrictions of injective equivariant coefficients, and then
into the exact published `AnalyticQuasiEtaleGlobalComparisonStatement`. The
finite-equivariant-refinement instance remains the original authorized
hypothesis.

`quasiEtaleComparisonIsoOfCompactTupleCones` is the actual resulting natural
isomorphism in each degree for a compact base with continuous action. The
forward morphism is definitionally the published `quasiEtaleComparison`, as
recorded by its `_hom` lemma.

The final theorem
`analyticQuasiEtaleGlobalComparison_of_tupleCones_liftCompatibilityStatement`
replaces the fixed-action compatibility input by the existing proposition
`QuasiEtaleLiftCompatibilityStatement K`. Compactness of the base supplies its
Hausdorff hypothesis, and the original target supplies continuity. This
identifies exactly the two outstanding geometric proof targets needed by this
route: compact compatible tuple cones and quasi-étale lift compatibility.

The provenance is internal composition of the published compatible-cover
derived-acyclicity and comparison reductions with the tuple-cochain
construction. This module proves conditional implications and constructs a
conditional natural isomorphism. It is not an unconditional proof of the
original comparison, and it supplies neither outstanding geometric proof.
