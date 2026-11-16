# Actual rational inverse and composition laws on formal atlas charts

This internal module verifies that rationalization of actual full-order
atlas isomorphisms preserves identity, inverse and composition. It also
proves that evaluating an actual full-order atlas quasi-isogeny on a
defined test chart preserves these three operations.

The scalar ring is a commutative domain with specified fraction field.
The coefficient ring is any commutative algebra over that scalar ring,
and the acting order is any algebra ring. The finite coordinate types
may differ. Covers may be infinite; the source and target covers of
each atlas map are equal. In the inverse and composition formulas,
`sourceChart` transports the chart index along precisely these cover
equalities. Test algebras use the coefficient-ring universe.

The proofs use extensionality for actual quasi-isogenies. Rationalization
then reduces to its defining tensor-Hom inclusion and its composition
equation. Chart evaluation reduces to the identity and composition
equations for actual atlas rational Hom; inversion retains the same
inverse chart map.

The provenance is internal, from `AtlasOrderRationalMorphism` and the
actual inverse and composition calculus in `OrderQuasiIsogenyCalculus`.
The assertions concern actual tensor maps with full-order commutation.
They do not assert comparison-refinement coherence, completeness of the
global tensor interface, preservation of heights, or framed equivalence
laws.
