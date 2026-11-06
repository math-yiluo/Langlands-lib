# Original number-field Weil adelic evaluation

This derived construction identifies the original-field map in the
number-field case of Brian Conrad, *Weil and Grothendieck approaches to
adelic points* (December 31, 2011), Example 4.2, printed pp.9–10.
Registered source: `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The source uses the natural equality of adelic point sets under Weil
restriction and proves equality of their independently constructed
topologies through integral models. This unit proves that the existing
original-field homeomorphism has exactly that natural underlying map.
Its proof applies the integral counit identity and the generic-fiber
counit compatibility.

Let K and L be number fields in an arbitrary common universe, with the
specified algebra map K → L. This is a finite extension. Let X be an
actual scheme with a specified immersion j : X → P^n_L, and use the
structure morphism j followed by P^n_L → Spec L. As in the imported
comparison module, this relative scheme is `originalScheme L X n j`.
The local finite-type hypothesis needed by the Weil construction follows
from the immersion. Neither a closed immersion nor affineness is assumed.

`adeleInclusion_compatible` proves that the literal full adele inclusion
`adeleInclusion : Adeles K →+* Adeles L` commutes with the original
diagonal field coefficients. The proof evaluates the two ring maps on
each element of K and uses `adeleInclusion_diagonal`.

The definition `adelicEvaluation` is the map

    (Res_(L/K) X)(Adeles K) → X(Adeles L).

Both point sets are actual scheme morphisms over the original fields,
as in `NumberFieldAdelePoints`. The definition is
`weilRestrictionEvaluation K L (Adeles K) (Adeles L)` with the literal
adele inclusion and the proved coefficient compatibility. Thus it
evaluates the original field Weil counit on the actual coefficient
test Spec(Adeles L) → Spec(Adeles K) ×_Spec(K) Spec(L). This definition
depends on neither an arithmetic model nor a chosen spread. All infinite
factors remain present.

For the comparison, take finite sets S and T of lower and upper finite
places and
`M : NumberFieldExtensionProjectiveModelData K L S T X n j`.
Write E = M.exceptional, E' for its full upper preimage,
A = O(K,E), B = O(L,E'), and Y = M.geometric.asOver.
These are actual arithmetic and geometric data: the lower model is
`affineChartWeilRestriction A B Y`, and the two original generic-fiber
isomorphisms are `lowerGenericFiberIso` and `upperGenericFiberIso`.
The published constructor `numberFieldExtensionProjectiveModel` supplies
such M for quasi-compact X. The model contains no assumed adelic
comparison or counit identity.

`adelicEvaluation_model` proves that evaluation of a lower full model
point after the lower spread identification equals integral evaluation
along the same adele inclusion followed by the upper spread
identification. It specializes
`projectiveModelWeilGenericFiberEvaluation_eq_integral` with the actual
adele rings. The proof explicitly retains the original A- and B-algebra
actions on those rings and supplies the towers through K and L using
their diagonal coefficient equalities. This avoids replacing an
original integral coefficient action by an unrelated inferred action.
Unfolding the spread equivalences gives precisely the base-change point
equivalences followed by the two generic-fiber isomorphisms in that
generic identity.

`adelicPointHomeomorph_eq_evaluation` identifies the existing original
field homeomorphism pointwise with `adelicEvaluation`. Every original
lower field point has a preimage under the actual lower spread
equivalence. On that preimage the existing homeomorphism's model law,
the full integral identity
`NumberFieldFixedModelWeilEvaluation.adelicPointHomeomorph_eq_evaluation`,
and `adelicEvaluation_model` give the result. The needed compactness of
Y's underlying space follows from its quasi-compact structure morphism
over an affine base, and its immersion is supplied by the model data.

`adelicPointHomeomorphOfSpreads_eq_evaluation` proves the same formula
for arbitrary independently specified finite-type spreads P and Q over
finite sets U and V. Their structure morphisms are locally of finite
type and quasi-compact, and their generic-fiber isomorphisms e and f
are specified. No separation hypothesis on P or Q is added. The
existing homeomorphism has each endpoint's independent
`numberFieldSpreadAdelePointTopology`; its underlying map is unchanged
by replacing the spreads. The proof applies that map identity and the
preceding canonical evaluation formula. Consequently the homeomorphism
for these topologies is the natural original-field Weil point
comparison.

Finally, `adelicPointHomeomorph_independent_model` proves that two
constructed arithmetic models M and M', even with different initial
finite supports, yield identical maps on every original lower adelic
point for the fixed original immersion j. Both maps equal
`adelicEvaluation`, which contains no model choice.

This unit supplies the canonical-map identification for the number-field
projective-immersion comparison. The function-field version, the
algebraic-space generalization and the other assertions of the
five-section paper remain separate obligations.
