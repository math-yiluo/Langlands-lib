# Proper maps on actual generic-fibre adelic points

`Langlands.Global.adelicSpreadProperMap` proves the exact proposition
`Langlands.Global.AdelicSpreadProperMapStatement`, with separate theorems for the
function-field and number-field clauses, in arbitrary common universe `u`.
The target is the proper-map assertion of Conrad (2011), printed p.11,
Proposition 4.4, on actual full-adele point carriers for arbitrary supplied spreads.

The implementation first derives finite type of the separated field target `W`
from its supplied finite-type spread and the inverse generic-fibre isomorphism.
It then invokes `curvePlaceSpreadProperExistence` or
`numberFieldSpreadProperExistence` to obtain separated finite-type arithmetic
models `M`, `N`, a proper model morphism `gm`, and generic-fibre isomorphisms whose
square with the prescribed field morphism `g` commutes. The initial finite set
is prescribed by the source spread; no relation to the target spread's finite
set is needed.

For those chosen models, the private `*_spread_proper_of_model` lemma conjugates
`curvePlaceFixedModel_proper` or `numberFieldFixedModel_proper` by the defining
spread point homeomorphisms. Naturality of the actual generic-fibre point
comparison and the commuting scheme square identify that conjugated map
pointwise with `p ↦ p ≫ g`. Composition of proper maps with homeomorphisms proves
properness on these field-point spaces.

Finally, the two arithmetic spread-topology independence theorems identify the
topologies from `M`, `N` with those from the originally supplied `X`, `Z`.
Rewriting both topology arguments gives the exact conclusion, retaining arbitrary
nonaffine schemes and potentially nonseparated initial models, finite constants
with the specified rational-function action in the curve clause, all infinite
number-field factors, and empty initial finite sets.

The target supplies the exact source provenance. This implementation follows the
model replacement in the first paragraph of Conrad's proof, then reuses the
fixed-model adelic properness theorem instead of reproving its local-field and
finite-level arguments. Imported predecessors are reused by Lean name and are
not part of this proof unit. Worker 208 authored the proof and its explanation;
Worker 1557 checked the proof against the published prerequisites and prepared
this proof-only pair for independent review.

The registered original is `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The model replacement is supported by printed pp.5–6, Theorem 3.4(1)–(3)
and Remark 3.5. The proof establishes only the proper-map assertion of
Proposition 4.4. Compactness, eventual stabilization and the remaining
five-section conclusions are separate obligations.
