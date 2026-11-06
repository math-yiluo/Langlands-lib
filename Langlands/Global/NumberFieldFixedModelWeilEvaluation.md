# Original full number-field Weil evaluation

This is a derived construction for Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), Example 4.2, printed
pp.9–10. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The unit identifies the existing original integral-model homeomorphism
with evaluation of the actual Weil counit along the literal full adele
inclusion. Its coordinate lemmas and descent argument are internal
comparisons over the existing constructions, not separately numbered
assertions in Conrad.

## Objects and scope

All rings and schemes inhabit the arbitrary common universe `u`.
`K` and `L` are number fields with a specified `K`-algebra structure on
`L`. Let `S` be any finite set of finite places of `K`, and let `S'`
be its full preimage in the finite places of `L`. Write `A` and `B`
for the actual rings of `S`-integers and `S'`-integers, respectively.
The scoped instances supply the original map `A → B` and its finite
projective module structure.

`numberFieldAdeleOver K S` has the actual full adele ring of `K` as
its underlying ring, with its original `A`-algebra action. It includes
all infinite and finite coordinates. Its enlarged stages
`numberFieldAdeleLevelOver K S T` retain that same `A` action.
`NumberFieldFixedModelAdelePoints K S W` is the type of actual
relative scheme morphisms `Spec(Adele K) → W`, not an auxiliary
restricted product of points.

For an arbitrary locally finite type `B`-scheme `Y`, the definition
`adelicEvaluation` evaluates its actual glued Weil restriction over
`A` on the literal ring map
`AdelicFunctoriality.adeleInclusion : Adele K →+* Adele L`.
`adeleInclusion_compatible` proves that this map respects the two
original integral bases. The evaluation is the existing
`weilRestrictionEvaluation`: its test morphism goes from
`Spec(Adele L)` to the base change of `Spec(Adele K)` and is then
composed with the original relative Weil counit. The definition
assumes neither compactness nor a projective immersion of `Y`.

The comparison with the existing homeomorphism additionally assumes
`CompactSpace Y.left` (Zariski quasi-compactness) and a specified
immersion `j : Y.left → ProjectiveSpace B n` over `B`. The immersion
need not be closed. Relative separatedness and underlying
quasi-separatedness are derived from this immersion and the affine
base; they are not additional caller hypotheses. The original
homeomorphism has the independently defined fixed-model final
topology on each endpoint.

## Coordinate construction

`fullFieldProjection` projects full adeles to an original completed
field, indexed by `OriginalPlace K`, the sum of original infinite
and finite places. `fullFieldProduct_injective` uses the actual
product and restricted-product coordinate extensionality.
`full_point_ext` shows that these coordinates determine points of
a relatively separated model with quasi-separated underlying
scheme. It derives reducedness from the injective map into the
product of fields, applies the existing separated coefficient
injectivity theorem, and then product-point injectivity.

`stage_pointField` proves that the literal stage inclusion preserves
each original completed-field projection. For an upper place above
an original lower place, `fullUpperFieldCoefficient` is the lower
full-adele projection followed by the original completion embedding.
Its compatibility lemma preserves the original integral bases.
`fullUpperFieldCoefficient_eq_projection` identifies that composite
with projection after the literal full adele inclusion. The proof
uses the actual comap/under equality of the two original places,
including the dependent completion types.

`adelicEvaluation_field` follows from upper coefficient naturality
of the original counit. `adelicEvaluation_stage_field` then follows
from lower coefficient naturality and the literal stage inclusion.
Thus each upper completed-field coordinate of full evaluation on a
stage is exactly `NumberFieldFixedLevelWeilEvaluation.fieldEvaluation`
on the original lower stage.

## Identity with the original homeomorphism

`adelicPointHomeomorph_stage_eq_evaluation` proves equality on every
original enlarged lower stage. It rewrites the existing full
homeomorphism by its original stage law and applies `full_point_ext`
to the upper model. For each upper original place it chooses its
actual lower comap or under-place, uses `stage_pointField`, the
published `levelPoint_fieldEvaluation_at`, and
`adelicEvaluation_stage_field`. All coefficient inclusions and
integral bases are unchanged.

`adelicPointHomeomorph_eq_evaluation` proves, for every actual lower
full-adele model point `p`,

```text
NumberFieldFixedModelWeilHomeomorph.adelicPointHomeomorph K S L Y n j hj p
  = adelicEvaluation K L S Y p.
```

The lower Weil model is locally finite type over the noetherian ring
`A`, hence locally finite presentation. The existing
`numberFieldFixedModelPointComparisonProperties` therefore supplies
an original arithmetic stage and a point on it whose literal
inclusion is `p`. Applying the stage identity proves the formula.
No global tensor-product isomorphism or new adelic comparison is
assumed.

This unit concerns original integral-model points in the number-field
case. Transport to the original field schemes through their actual
generic-fiber isomorphisms, the function-field analogue, and the
remaining whole-paper assertions remain separate obligations.
