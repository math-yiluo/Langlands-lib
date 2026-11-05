# Hausdorff actual adelic points of separated field schemes

`Langlands.Global.adelicSpreadSeparated` proves exactly
`Langlands.Global.AdelicSpreadSeparatedStatement` at arbitrary common universe
`u`. The actual full-adele point carriers and the specified-spread topologies
are those already defined in the target's imports. Separation is assumed only
for the original field scheme `Y`, with no separatedness or affineness premise
on its finite-type arithmetic model `M`.

## Product model

The shared `finiteType_overProd` from `AdelicSpreadProductProof` proves that
`M ⨯ M` is finite type over
the same arithmetic base. Its first projection is a base change of the
second factor's structure map, hence locally of finite type and quasi-compact.
Composing with the first factor's structure map gives the two corresponding
properties of the product structure map. No separation is used.

The generic-fiber pullback functor preserves binary products.
The shared `productModelIso` from the same module combines this preservation
with two copies of the specified
generic-fiber isomorphism `e`. Uniqueness of limiting binary fans gives an
isomorphism from the generic fiber of `M ⨯ M` to `Y ⊗ Y`, the existing
cartesian monoidal product over the field. Applying `adelicSpreadProduct`
to this chosen product model gives a homeomorphism from its actual adelic
points to the product of the two original point spaces, with exactly their
specified-spread topologies.

## Closed field diagonal

The scheme map underlying `lift (𝟙 Y) (𝟙 Y)` is definitionally
`pullback.diagonal Y.hom`. The target's `IsSeparated Y.hom` instance makes it
a closed immersion; `diagonal_closed` records this fact.
`adelicSpreadClosedImmersion`, applied to this field morphism and the chosen
models `M` and `M ⨯ M`, makes its actual adelic point map a closed embedding.
This does not require the diagonal to descend to a closed immersion of the
chosen arithmetic models.

The private `point_t2` composes that closed embedding with the product
homeomorphism. The categorical projection identities identify the composite
with the ordinary map `p ↦ (p, p)`. Its image is the topological diagonal,
which is therefore closed. Mathlib's `t2_iff_isClosed_diagonal` proves
Hausdorffness of the original point topology.

## Arithmetic scope and provenance

The proof applies this same construction in both arithmetic clauses.
Function fields retain arbitrary perfect constants, the specified
rational-function action and scalar tower, and potentially inseparable
extensions. No finite-constant or local-compactness premise is added.
The number-field clause uses the full adele ring, including every infinite
factor. All finite place sets, including the empty set, remain allowed.
Existence of a model and its generic-fiber isomorphism are explicit target
inputs and are not conclusions of this proof.

The source is Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (December 31, 2011), registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`, printed
p.9, Section 4. The source asserts Hausdorffness for separated finite-type
schemes over global fields with the final adelic topology. The target
Markdown explains the derived specified-spread formulation and its
arbitrary-perfect-constant extension. The proof above implements its
closed-diagonal argument, using the independently proved product and
closed-immersion comparisons rather than separation of the chosen spread.
It proves this focused target and does not assert whole-paper completion.

Worker 208 authored this pair. The two product-model helpers and the point
diagonal argument are reused and generalized from that worker's earlier
product and group drafts. The product and closed-immersion proofs are imported by Lean name from
the published Library. This contribution contains only the new proof and
its paired explanation. Worker 1218 checked the theorem against the published
inputs and prepared the focused submission.
