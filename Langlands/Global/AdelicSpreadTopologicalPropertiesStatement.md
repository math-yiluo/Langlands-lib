# Topological properties of actual adelic points from a specified spread

`AdelicSpreadTopologicalPropertiesStatement` transfers the fixed-model
topological results to actual full-adele points of the generic fibre
identified by a specified spread. It asserts local compactness and
second countability, and Hausdorffness when the arithmetic model is
separated. It concerns the defined spread topology on the actual point
space; no topological property or comparison map is assumed.

For each finite set `S`, the arithmetic model `X` is a scheme over the
actual outside-`S` integer ring. Its structure morphism is locally of
finite type and quasi-compact. The scheme `Y` is over the original global
field, and `e` is any specified isomorphism from the actual generic
fibre of `X` to `Y`. The carriers `CurvePlaceAdelePoints` and
`NumberFieldAdelePoints` are actual relative scheme morphisms from the
spectrum of the full adele ring over that field. The topologies
`curvePlaceSpreadAdelePointTopology` and
`numberFieldSpreadAdelePointTopology` transport the arithmetic-stage
final topology along the pullback-adjunction point equivalence and `e`.
Their existing spread point homeomorphisms supply the property transfer.

The target quantifies an arbitrary common universe `u`, nonaffine
finite-type models and every finite `S`, including empty `S`. The
function-field clause keeps the original finite constant field, its
scalar action and the compatible rational-function presentation with
`FunctionField k F`; it adds no separability condition. Finite fields
are perfect, as needed by the existing generic-fibre diagonal. The
number-field clause includes every infinite completion. Local
compactness and second countability impose no separation assumption.
Only the Hausdorff conclusion assumes `IsSeparated X.hom`.

The source is Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (December 31, 2011), printed pp.6 and 9, the point identification
(3.5.1), Corollary 3.7 and the opening of Section 4. Section 4 asserts
local compactness, Hausdorffness and a countable base for separated
finite-type schemes over the global field. The present target is a
derived intermediate formulation for an arbitrary specified model.
The fixed-model theorems prove local compactness and second countability
also without separation and for empty `S`, by continuous open coverage
from actual arithmetic stages. The spread point homeomorphisms
transport those conclusions without adding hypotheses.

This target does not claim that every field scheme has a spread, does
not supply model independence, and does not replace separation of `X`
by separation of `Y` in the Hausdorff clause. The unrestricted
separated-generic-fibre assertion additionally requires existence of a
separated spread or descent of separatedness after enlargement. Those
are separate geometric results. This file defines a proposition to be
proved and makes no claim of whole-paper completion.

Registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`,
printed pp.6 and 9, (3.5.1), Corollary 3.7 and Section 4.
