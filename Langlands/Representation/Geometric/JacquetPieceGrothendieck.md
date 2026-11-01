# Actual geometric pieces after source Jacquet restriction

Author: Worker 165.

This internal derived helper compares actual integer-linear maps on the full
exact finite-length smooth complex Grothendieck group. It retains arbitrary
p-adic fields, supplied topological data, independent field and carrier
universes, saturated carriers and all natural ranks. No classification or
irreducible-image result is used.

`blockShape_eq_of_conjugatesLevi_same_target` shows that a fixed permutation
and target standard Levi determine the source standard block shape. Injectivity
of mapping subgroups through actual matrix conjugation gives equality of the
source embedded Levis. The published standard-Levi uniqueness theorem then
gives equality of their ordered positive block shapes.

`jacquetGeometricTerm` first applies actual normalized Jacquet restriction to
its source block shape. It transports by actual inverse whole-Levi conjugation
to the flattened target refinement, changes to the literal refined subgroup
coordinates, and applies actual normalized refined induction inside the target
product Levi. `jacquetGeometricTerm_eq` proves that the map is independent of
any construction of its standard source shape, when its target refinement and
permutation agree. This is equality of actual maps on every virtual class.

`geometricPieceK0_comp_jacquetK0` identifies the actual geometric-piece map
after normalized Jacquet restriction to the source outer shape with that term.
The proof first uses the published actual factorization of a geometric piece
as refined Jacquet restriction, inverse intersection transport and refined
induction. The existing flattened intersection comparison identifies the middle
map with whole-Levi inverse transport. The actual flattened Jacquet comparison
and restriction in stages replace the successive restrictions by normalized
Jacquet restriction to the flattened source shape. Injectivity of the flattened
coordinate equivalence then proves equality before refined induction.

Both intersection assumptions are literal equalities of the actual embedded
subgroups. This helper proves no geometric-lemma formula, cancellation or full
Aubert compatibility. Its purpose is the actual-map comparison needed before
fixed-permutation signed cancellation. All input construction, transitivity,
coordinate and statement pairs are reused unchanged. The provenance is an
internal consequence of the imported published constructions and comparisons;
no additional original-literature assertion is transcribed.
