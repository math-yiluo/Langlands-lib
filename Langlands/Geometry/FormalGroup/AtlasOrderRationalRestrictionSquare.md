# Actual rational restriction squares on defined finer formal charts

This internal module gives the actual rational commuting square
for restricting a full-order atlas quasi-isogeny to a specified
principal-cover refinement.

`onChart_restrict` identifies the entire restricted
quasi-isogeny on a defined finer chart with the route through
the source refined-chart isomorphism, the original
quasi-isogeny on its selected original chart, and the inverse
target refined-chart isomorphism. The target refinement is
exactly the source refinement retargeted along the supplied
equality of original covers.

The proof uses forward-map extensionality for actual full-order
quasi-isogenies and the existing actual rational-Hom chart
restriction equation. Thus both inverse maps also agree.

`restrictionChartSquare` packages the actual restricted map,
the two actual chart identifications, the original chart map
and the proved commuting equation. The proof applies the
restriction formula and cancels the target inverse pair using
the actual quasi-isogeny inverse equations.

The scalar ring is a commutative domain with specified fraction
field, the coefficient ring is any commutative scalar algebra,
and the acting order is any algebra ring. The two finite
coordinate types may differ. Original covers agree, while
both original and finer covers may be infinite. Test algebras
use the coefficient-ring universe. A defined finer chart
requires its actual generator to map to a unit.

The provenance is internal from actual rational atlas
restriction and the actual formal chart identifications.
No equality of formal maps is inferred from point equality.
Framed-comparison refinement/composition, comparison-chain
collapse, height statements, coefficient descent and
representability remain separate.
