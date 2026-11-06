# Cofinal upper supports for the fixed-model Weil comparison

This is a derived direct-limit ingredient for Conrad, *Weil and
Grothendieck approaches to adelic points* (2011), Example 4.2, printed
pp.9–10. It uses the existing actual-place restriction maps and finite
full preimages. The number-field branch includes all infinite places in
every stage. The curve branch retains the finite constants, original
rational-function action and scalar towers, finite upper extension and
initial principal support of the fixed-model comparison. No separability
is required. All fields share an arbitrary universe.

`numberFieldUpperLevelFunctor` and `curveUpperLevelFunctor` send an
arbitrary finite lower support above the fixed initial support to its
full upper preimage. Their monotonicity theorems prove that these are
functors on the actual directed support orders. `numberFieldLevelCover`
and `curveLevelCover` give explicit lower enlargements for any prescribed
finite upper support: take the union of the initial lower support with
the image of the prescribed upper support under actual place restriction.
The cover specification theorems reuse the existing union-image coverage
lemmas. They prove that the prescribed upper support is contained in the
full preimage of the constructed lower enlargement. Mathlib's criterion
for monotone functors between directed orders then proves both functors
final. These maps agree literally with the `upperLevel` maps used in the
existing fixed-base level homeomorphisms.

For an actual upper integral model Y that is locally of finite type and
quasi-compact over its integral base, `numberField_continuous_iff` and
`curve_continuous_iff` show that a map from its actual full-adele points to
any topological space is continuous exactly when its restrictions to the
full-preimage stages are continuous. The full point space retains its
existing fixed-model final topology and every source stage its existing
fixed-model stage topology. This does not assume separatedness or
bijectivity of stage maps.

The proof uses the existing final-topology continuity criterion. One
direction restricts to the full-preimage stages. In the other direction,
cover any prescribed upper stage by the concrete full-preimage stage
above. Its coefficient inclusion is continuous by the proved fixed-model
transition theorem. In the curve branch, the upper rational-function action and function-field
finiteness are derived from the original compatible tower and finite
extension. Composing with the continuous restriction to the larger stage
yields continuity on the prescribed stage. Composition of
the two literal coefficient inclusions is proved equal on actual point
morphisms using contravariant spectrum functoriality.

This unit proves cofinality and its topology consequence. Naturality of
the finite-level Weil homeomorphisms and assembly of the full adelic
comparison remain separate obligations.
