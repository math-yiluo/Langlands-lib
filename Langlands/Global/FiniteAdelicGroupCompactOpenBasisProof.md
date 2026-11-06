# Compact open identity neighborhoods on actual finite adelic points: proof

`finiteAdelicGroupCompactOpenBasis` proves the exact published
`FiniteAdelicGroupCompactOpenBasisStatement` at unrestricted universe `u`.

`finiteAdeles_totallyDisconnectedSpace`: each original finite completion
is ultrametric and hence totally disconnected by pinned Mathlib. The
coefficient map from the actual
restricted finite adele ring to the full product of those completions is
continuous and injective. A connected subset therefore maps to a
subsingleton, and injectivity gives the same conclusion in the restricted
product. No assertion that this map is an embedding is used.

`finiteAdelicGroupPoints_totallyDisconnectedSpace`: for an affine group
scheme, the existing regular-function evaluation map
`isEmbedding_affinePointEvaluation` embeds its actual finite adelic points into the product of copies of the
same coefficient ring. The product is totally disconnected, giving the
first conclusion without finite type.

Under the additional local finite-type hypothesis, the published original
finite adelic point topology is locally compact and Hausdorff. The
Library's `isLocallyProfinite_of_mathlib` and public `vanDantzig` yield an
actual compact open subgroup in every identity neighborhood. Conversely,
an open subgroup is itself an identity neighborhood, so any superset is
one too. These two implications are precisely the required `HasBasis`.

The proof is an internal original-topology specialization of published
project topology and pinned Mathlib. It introduces no reductivity or
splitting premise and no alternate point group or topology. It is
submitted as the focused exact-target proof of the published statement,
for independent review and exact-target validation.
