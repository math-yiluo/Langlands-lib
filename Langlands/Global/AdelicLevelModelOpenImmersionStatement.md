# Open immersions on actual arithmetic-level model points

## Target and mathematical scope

`Langlands.Global.AdelicLevelModelOpenImmersionStatement` is the conjunction
of a function-field clause and a number-field clause. Each clause has two parts.

1. **Embedding.** Let `f : X ⟶ Y` be a morphism of schemes over the
   `S`-integers whose underlying scheme map is an open immersion. Assume the
   target `Y` is of finite type, stated as the separate Lean assumptions
   `LocallyOfFiniteType Y.hom` and `QuasiCompact Y.hom`. Then postcomposition
   `p ↦ p ≫ f` is a topological embedding (`IsEmbedding`) from the level points
   of `X` to the level points of `Y`. Neither model is assumed affine or
   separated.
2. **Image need not be open.** For the actual open inclusion
   `affineLinePunctureι` of the punctured affine line (the multiplicative group)
   into the affine line over the `S`-integers, the image of the induced map on
   level points is not open in the level points of the affine line. So the
   embedding in part 1 is not an open embedding in general.

The point spaces are the actual relative points `RingPoint` with values in the
adelic level ring. They carry the published level topologies
`curvePlaceLevelModelPointTopology` and `numberFieldLevelModelPointTopology`.
These topologies are induced by the actual local-model point map into the
product of the local point spaces. That product is the product topology of
Theorem 3.6.

`CurvePlaceLevelModelOpenImmersionStatement` covers every specified finite
extension `F` of `RatFunc k` over an arbitrary constant field `k`, with the
`k → RatFunc k → F` scalar tower retained. It uses the curve-place `S`-integers
`curvePlaceSIntegers k F S` and the level ring `curvePlaceAdeleLevel k F S`.
`NumberFieldLevelModelOpenImmersionStatement` covers every number field `K`. It
uses the `S`-integers `(S : Set (FinitePlace K)).integer K` and the full level
ring `numberFieldAdeleLevel K S`, which includes every infinite completion. In
the curve clause `S` is an arbitrary finite set of curve places (discrete
places of `F` trivial on `k`). In the number-field clause it is an arbitrary
finite set of finite places, the infinite places being always present. Either
may be empty. The combined statement takes both clauses in one common universe.

## Source and provenance

Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), registered as `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The paragraph after the proof of Theorem 3.6 (printed pp.8–9) reads: "For open
immersions `U_S ↪ X_S` it is not true in general that
`U_S(A_{F,S}) → X_S(A_{F,S})` is an open embedding, though it is a topological
embedding. Indeed, an arbitrary product of open embeddings is a topological
embedding but usually does not have open image." In that paragraph `X_S` is a
finite type scheme over the `S`-integers, so the Lean statement assumes that the
target is of finite type.

Conrad gives no specific example in this remark. The punctured affine line in
part 2 is this formalization's witness for "not true in general". It is the
example of Conrad's printed pp.3–4 and p.11 (the inclusion of units into the
ring), here at a finite level. At level `S` its image is the set of level
elements that are units in every factor. In the product topology this is a
product of proper open subsets of infinitely many integral factors, so it is
not open. Part 2 asserts only this non-openness, not this argument.

Conrad states the remark for a global field `F`. Taking both characteristics,
and an arbitrary constant field in the function-field case, is this
formalization's reading of that scope; the product argument does not use
finiteness of the constant field. The full adelic analogue, failure of
embedding for the punctured line on full adelic points, is the separate
`AdelicPunctureEmbeddingStatement`. The closed-immersion counterpart at the
level is `AdelicLevelModelClosedImmersionStatement`.

This file supplies a proposition-valued statement, not a proof.
