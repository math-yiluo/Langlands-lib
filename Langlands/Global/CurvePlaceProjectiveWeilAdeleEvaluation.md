# Original function-field Weil adelic evaluation

This derived construction identifies the original-field map in the
function-field case of Brian Conrad, *Weil and Grothendieck approaches to
adelic points* (December 31, 2011), Example 4.2, printed pp.9–10.
Registered source: `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Conrad uses the natural equality of adelic point sets under Weil
restriction and proves equality of their independently defined topologies
through integral models. This unit identifies the underlying map of the
existing original-field homeomorphism with that natural counit map.
The proof uses the full integral counit identity and the generic-fiber
counit compatibility.

Let k, K and L be fields in an arbitrary common universe, with finite k,
compatible k- and K-algebra structures, a specified compatible function-field
presentation of K over RatFunc k, and finite-dimensional L over K.
No separability assumption on L/K is imposed. The compatible RatFunc k
algebra structure and function-field presentation of L are derived
internally by composition and transitivity of module finiteness. The
local notation `withUpper%` introduces these derived instances in both
declaration types and their terms; it adds no hypothesis on L.
The finite constant field and lower presentation are the scope of the
arithmetic model and diagonal constructions used here.

Let X be an actual scheme with a specified immersion
j : X → P^n_L. Its original L-structure is j followed by the projective
space structure map; this is `originalScheme L X n j` from the imported
homeomorphism module. Local finite type follows from the immersion.
Neither a closed immersion nor affineness is required.

`adeleInclusion_compatible` proves that the published literal map
`curvePlaceAdeleInclusion k K L` preserves the original diagonal field
coefficients. Ring homomorphism extensionality reduces this assertion
to its published diagonal formula.

The definition `adelicEvaluation` is the map

    (Res_(L/K) X)(CurvePlaceAdeleRing k K)
      → X(CurvePlaceAdeleRing k L).

These are the actual original-field scheme point sets
`CurvePlaceAdelePoints`, with all curve places and their original
completed fields. The definition specializes
`weilRestrictionEvaluation` to the literal full adelic inclusion and
the coefficient compatibility just proved. It evaluates the actual
field Weil counit on the induced coefficient test spectrum.
It contains no arithmetic model, parameter, exceptional
support, or chosen spread.

For the comparison, take s ∈ K with K finite-dimensional over k(s),
finite lower and upper supports S and T, and actual data
`M : CurvePlacePrincipalProjectiveModelData k K L s S T X n j`.
Write E for the principal exceptional set defined by s and M's nonzero
denominator, and E' for its full upper preimage. The original integral
bases are A = O(K,E) and B = O(L,E'). The upper model is
Y = M.geometric.asOver and the lower model is the actual
`affineChartWeilRestriction A B Y`.
The two generic-fiber isomorphisms are `lowerGenericFiberIso` and
`upperGenericFiberIso`. The published
`curvePlacePrincipalProjectiveModel` constructor supplies these data
for quasi-compact X. The data contain no assumed adelic comparison.

`adelicEvaluation_model` proves that field evaluation of a lower full
model point after its spread identification equals integral evaluation
followed by the upper spread identification. It applies
`projectiveModelWeilGenericFiberEvaluation_eq_integral` to the actual
full curve adele rings, presented as the fixed-base coefficient rings
`curvePlaceAdeleOver`. The proof explicitly retains both original
integral algebra actions and the field actions, and supplies their
scalar towers using `curvePlaceAdeleLevelDiagonal_eq`. Unfolding the
spread equivalences and generic-fiber isomorphisms reduces them to the
base-change point equivalences in the general identity. The final
conversion is by definitional equality.

`adelicPointHomeomorph_eq_evaluation` proves pointwise equality of the
existing original-field homeomorphism with `adelicEvaluation` on
every original lower adelic point. Surjectivity of the lower spread
equivalence represents that point by an actual full integral model
point. The homeomorphism's model law, the full integral identity
`CurvePlaceFixedModelWeilEvaluation.adelicPointHomeomorph_eq_evaluation`,
and `adelicEvaluation_model` then give the equality. The model supplies
its relative projective immersion; quasi-compactness over its affine
base supplies compactness of its underlying Zariski space.

`adelicPointHomeomorphOfSpreads_eq_evaluation` proves the same formula
for independently specified spreads P and Q over arbitrary finite
supports U and V, with specified generic-fiber isomorphisms. Their
structure morphisms are locally of finite type and quasi-compact.
No separation hypothesis on P or Q is added. The imported
homeomorphism uses each endpoint's independently constructed
`curvePlaceSpreadAdelePointTopology`. Its underlying map equals the
constructed-model homeomorphism's map, so the preceding identity
identifies it with the canonical field counit as well. Thus the
natural field comparison is a homeomorphism for these independently
defined topologies.

Finally, `adelicPointHomeomorph_independent_model` allows a second
parameter s', different initial finite supports S' and T', and
different constructed model data M', retaining the same original
immersion j. The two maps agree on every original lower adelic point
because both equal `adelicEvaluation`.

This unit supplies the canonical-map identification for the original
function-field projective-immersion comparison, including inseparable
finite extensions. Algebraic spaces, the separate tensor-ring
identifications, and the other assertions of the five-section paper
retain their own obligations.
