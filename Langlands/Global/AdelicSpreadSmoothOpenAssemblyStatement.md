# Conrad's Theorem 4.5 from its model, local and almost-all inputs

This derived statement records the final assembly in the proof of Theorem 4.5
of Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed pp.12–13. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
By his Theorem 3.4(2), Conrad chooses smooth surjective separated
finite-type models with geometrically connected fibres over a ring of
S-integers. Varying through finite supersets of S, he reduces openness on
adelic points to products of local maps, which are open by smoothness. For
all but finitely many places he shows that the integral map is surjective, by
the uniform Lang–Weil estimate of his Lemma 4.6 and Hensel's lemma. This module states
that these separately formalized inputs imply the theorem. It contains no
proof.

## The statements

`CurvePlaceSpreadSmoothOpenAssemblyStatement` is an implication. Its five
premises are the following published proposition definitions, and its
conclusion is `CurvePlaceSpreadSmoothOpenStatement`, the function-field
clause of Theorem 4.5 for arbitrary finite-type spreads of source and target.

1. `UniformLangWeilStatement`, the uniform Lang–Weil estimate of Lemma 4.6.
2. `CurvePlaceLevelComponentSurjectivityStatement`: given uniform Lang–Weil, a
   smooth, separated, quasi-compact, geometrically connected morphism of
   models whose target has finite type over the integers is surjective on
   actual integral points at cofinitely many local factors of every enlarged
   level.
3. `CurvePlaceSmoothLocalPointOpenStatement`: smooth maps of separated
   finite-type models are open on the points at every actual local factor of
   every enlarged level.
4. `CurvePlaceFixedModelAdeleOpenOfLocalStatement`: for a fixed pair of
   separated finite-type models, local openness at every factor together with
   cofinite surjectivity at every enlarged level gives openness of the actual
   fixed-model adelic point map.
5. `CurvePlaceSpreadMorphismPropertyExistenceStatement` for
   `Smooth ⊓ GeometricallyConnected`: a smooth geometrically connected map of
   separated finite-type schemes over the function field has compatible
   separated finite-type models at some enlarged level. The model map has the
   same two properties.

`NumberFieldSpreadSmoothOpenAssemblyStatement` is the same implication for a
number field, with the corresponding `NumberField...` premises and the
conclusion `NumberFieldSpreadSmoothOpenStatement`. Every infinite factor of
the full adeles remains present in the local and fixed-model premises.
`AdelicSpreadSmoothOpenAssemblyStatement` is the conjunction of the two, in an
arbitrary common universe `u`.

## Relation to the source and derived content

The decomposition into these five inputs is derived from Conrad's proof. It is
not a separately stated result of the paper. Each premise is a published
proposition definition whose Markdown explains its own relation to the
source. Premise 2 needs a target model of finite type over the integers.
Conrad's proof applies Lemma 4.6 to schemes of finite type over the integers.
In the proof this is arranged by enlarging the level to a cofinal principal
level whose integer ring has finite type over the integers.

The statement does not prove any premise. Uniform Lang–Weil in particular
remains a separate obligation. A proof of this statement establishes Theorem
4.5 exactly when proofs of all five premises are available.
