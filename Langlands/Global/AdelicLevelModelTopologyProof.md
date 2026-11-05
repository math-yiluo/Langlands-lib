# Proof of the actual adelic-level topology comparisons

Authors: Worker 208 (proof and initial Markdown); Worker 59 (verification and
submission).

`adelicLevelModelTopology` proves exactly
`AdelicLevelModelTopologyStatement` in every common universe u. The point
carriers, coefficient maps, arithmetic scalar actions and pullback models are
the original constructions. The source topologies are the explicitly defined
arithmetic induced topologies, and the targets are the products of the
independently constructed local scheme-point topologies.

For the affine comparison, `schemePointTopology_eq_affine` first identifies
each actual local model's scheme-point topology with its independently
constructed affine evaluation topology. Taking the dependent product gives
`localModelPointProductTopology_eq_affine`. The existing actual arithmetic
coordinate map is a homeomorphism for affine evaluation topologies, by the
separate `AdelicLevelModelComparisonProof`. Its inducing identity therefore
identifies the induced source topology with the original affine evaluation
topology. The proof also records the generic
`localProductPointTopology_eq_affine` comparison.

For a quasi-compact quasi-separated model, the separate actual-coordinate
comparison gives injectivity and surjectivity. The defining inducing
property of the arithmetic source topology, together with injectivity,
makes the map an embedding; surjectivity makes this a homeomorphism.

For a finite-type model, the proof uses the independently stated arithmetic
bijection from `AdelicFiniteTypeLevelModelComparisonProof`. That result uses
Noetherianity of the actual S-integer base to deduce quasi-separatedness
from local finite type, and uses quasi-compactness of the structure morphism
to deduce quasi-compactness of the source scheme. The same inducing plus
bijective argument then proves the homeomorphism without adding an affine,
separated or quasi-separated premise.

This implements the product-topology transport in Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed
pp.6–8, Theorem 3.6, with the extensions and precise application boundaries
recorded in the target Markdown. Registered contextual source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The homeomorphism for the defined source topology does not itself prove model independence or transition-map
openness. Those assertions, the global adelic colimit, the conventional
function-field realization and the algebraic-space comparison remain
separate obligations.
