# Proper arithmetic model reduction

Authors: Worker 129 and Worker 157. Reused draft arguments: Worker 208 and Worker 105.

This internal derived helper keeps `SpaceLimitMorphismDescent` and the properness
case of `SpaceLimitPropertyDescends` as explicit premises. It does not prove either
descent premise or assert an unconditional proper-model theorem.

The source is Brian Conrad, *Weil and Grothendieck approaches to adelic points*,
December 31, 2011, registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Printed pp.5–6 give Theorem 3.4, p.13 extends the theorem to algebraic spaces,
and p.11 and the paragraph before Proposition 5.8 on p.17 use proper-model
replacement. The names and intermediate packaging here are internal derived
content.

`adelicSpaceProperModel_of_descent` proves the unchanged
`Langlands.Global.AdelicSpaceProperModelStatement.{u}` from exactly the two
explicit descent premises above, in arbitrary common universe `u`. Its two
component theorems keep all supplied-model hypotheses, the given field arrow,
and the exact commuting generic-fibre square. In the function-field case the
constant field is finite and the original nonempty-set hypotheses are retained.
The number-field case allows empty initial sets. This conditional theorem does
not discharge Task 5358's unconditional proof target.

`ProperStageModel D c g` is the type of proper stage models of an actual arrow
`g : Y ⟶ W` between spaces over the point of a cone `c` on a scheme diagram
`D`. It stores a stage, two algebraic spaces at that stage, their separatedness
and locally finitely presented quasi-compact atlas conditions, isomorphisms of
their base changes to `Y` and `W`, a proper map, and the exact commuting square
with `g`. This data type itself requires only a small indexing category and a
cone, with no affine, cofiltered, or limit assumption. Those further hypotheses
enter the constructor.

`properStageModelOfDescent` noncomputably chooses a value of this type from the
existence theorem below. It takes the two geometric descent statements as
explicit hypotheses, an actual cofiltered limit of affine schemes, compatible
maps to an affine base, the two supplied separated models with the atlas
conditions, the generic-fibre identifications, and the proper arrow. Its stored
properties follow from `exists_proper_model`; choosing a witness does not add
an assumption or change the commuting square. Both arithmetic component
proofs use this constructor and extract its stored fields.

`exists_proper_model` applies to a cofiltered affine scheme diagram with its
limit and compatible maps to an affine base. Both supplied base spaces are
separated and have a single atlas whose structural morphism is locally of finite
presentation and quasi-compact. Given identifications of their limit fibres with
two spaces and a proper morphism between these latter spaces, it produces a stage,
separated models with the same atlas conditions, identifications of their limit
fibres, and a proper stage morphism whose base change commutes with the original
proper morphism.

The Lean proof conjugates the given arrow by the supplied identifications, applies
morphism descent, and translates its section equality into an equality of arrows.
Properness is transported through the comparison isomorphisms. Properness descent
then gives a further stage. Naturality of the iterated-base-change comparison
retains the exact commuting square at that stage. Separatedness and atlas conditions
are preserved by base change.

For each arithmetic branch the proof first replaces the original finite sets
`S` and `U` by their union `V`. It base changes both supplied models to the
`V`-integer ring and composes the generic-fibre comparisons with the original
isomorphisms. Published Noetherianity of the original integer rings turns the
supplied finite-type atlases into locally finitely presented quasi-compact
atlases; these atlas conditions then survive base change. The geometric helper
is applied to the actual spectrum diagram of integer rings indexed by finite
sets containing `V`, using its published field-colimit proof. The models
obtained at a stage have finite-type atlases. In the function-field case the
final finite set is nonempty because it contains the original `S`.

The supporting lemmas prove that separatedness implies quasi-separatedness,
that the four defining components of properness transport through arrow
isomorphisms, and the two atlas implications just used. The section-equality
conversion uses functoriality of pullback along the identity of each test scheme;
the properness transport uses the diagonal relative closed-immersion property
and the published transport lemmas for quasi-compactness, local finite type,
and universal closedness.

The `compIso_hom_comp_eq` proof is adapted from Worker 208's shared, unreviewed
`AdelicSpaceSpreadIndependenceProof` draft, revision 1, for Task
`360a1cdf-4b68-402e-b087-254b03da61f6`. Its argument is reproduced here; no unreviewed
module is imported.
The arithmetic spectrum-diagram specializations follow the same draft's
`curve_exists_level_hom` and `numberField_exists_level_hom` arguments.
The union-base generic-fibre comparisons adapt Worker 105's
`curveGenericFiberIso` and `numberFieldGenericFiberIso` from the
`AdelicSpaceSpreadInitialSet` module in the same shared draft revision.
