# Continuity, openness and separated injectivity of actual DVR points

Author: Worker 105. Verification, documentation and submission: Worker 1363.

This proof targets exactly `DvrSchemePointProperties R K`. With the prescribed maximal-ideal valuation on K and induced topology on R, the coefficient inclusion is inducing and injective. Addition, multiplication and negation on R are continuous because their composites with the inclusion are the corresponding continuous operations on K. Thus R is a topological ring for precisely the topology in the statement.

The range of the inclusion is the valuation subring, by Mathlib's valuation bound on R and `IsDiscreteValuationRing.exists_lift_of_le_one`. That subring is open, so the inclusion is an open embedding. The existing actual scheme coefficient-change theorems give continuity and openness, the latter using the specified local finite-type hypothesis. The actual base-change topology theorem gives a homeomorphism from X(K), viewed relative to R, to the K-points of the actual generic fiber with its own chart topology. Composition gives continuity and openness of the exact map in the target.

When X is separated over Spec R, the coefficient-change injectivity theorem applies because R is reduced and the fraction-field inclusion is injective. The base-change equivalence preserves injectivity. A continuous injective open map is an open embedding. No completeness, residue-field finiteness, global finite type, affineness or quasi-compactness hypothesis is introduced. The source passage and the reason for the generalization beyond its stated complete finite-type setting are explained in the target Markdown.


The proof reuses `schemeCoefficientContinuity_proof`, `schemeCoefficientOpen_proof`, `schemeSeparatedCoefficientInjectivity_proof`, and `schemeBaseChangeTopology_proof` from their independently published modules. The intermediate R-relative K-point space also carries its own `schemePointTopology`; composing with `ringPointBaseChangeEquiv R K K X` yields the precise generic-fiber target topology, rather than defining that topology by transport.

Provenance: Brian Conrad, *Weil and Grothendieck approaches to adelic points*, December 31, 2011, proof of Theorem 3.6, printed page 8 (registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`). The arbitrary-DVR and locally finite-type scope is a derived generalization of the complete-DVR finite-type local step in that passage. This proof establishes that local scheme statement only; adelic products, transition topologies, descent, algebraic spaces and whole-paper completion require their separate results.
