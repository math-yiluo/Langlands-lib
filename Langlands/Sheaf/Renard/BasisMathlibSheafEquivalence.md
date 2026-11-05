# Chosen-basis sheaves and actual Mathlib sheaves

This companion to `BasisAllOpenEquivalence` composes its actual
compatible-family equivalence with the published all-open/Mathlib
comparison. All declarations are in
`Langlands.Sheaf.Renard.BasisMathlib`. It constructs

```lean
BasisMathlib.equivalence.{u,v} (B : OpenBasis X) :
  BasisSheaf.{u,max u v} B ≌
    TopCat.Sheaf AddCommGrpCat.{max u v} (TopCat.of X)
```

The space has its supplied topology, and the actual chosen basis is
arbitrary. The universes `u` and `v` are independent. Compatible families
indexed by the space fit in the sufficient section universe `max u v`.
This is an internal implementation convention, not an attributed source
error or an arbitrary original-`v` extension claim. The reverse restriction
functor separately works at every independent section universe `v`.

## Source and provenance

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The definitions are II.2.1, printed pp.33–34 / one-based PDF39–40; the
final paragraph of II.2.1, printed p.37 / PDF43, asserts the
chosen-basis/all-open equivalence by germ extension and restriction.
A.VI.1, printed p.261 / PDF267, supplies the abelian-group sheaf example
motivating the subsequent separate abelianness proof. All four original
pages were read directly for this work.

The supplementary historical 2010-edition errata, registered as
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF2–3, were also read. The nearby cover-index and adjunction corrections
do not change this composition. The public source note
`notes/renard/basis-sheafification-source.md` records the repair of the
printed separation step; the imported construction uses separation only
for actual sheaves. No separation of arbitrary raw presheaves is used.

The book does not discuss Mathlib. This composite equivalence, its
categorical data, and all evaluated comparisons are internal elaborations
of the cited source assertion. The imported `BasisAllOpenEquivalence`
implements the canonical extension by compatible families of original
sections and proves its literal sheaf condition and unit/counit laws.
`AllOpenMathlibSheaf` supplies the actual all-open/Mathlib equivalence with
identity section comparisons. This module imports and composes those
constructions, without assuming an equivalence as an extra parameter.

## Actual functors and forgetful comparisons

| Name | Construction and hypotheses |
| --- | --- |
| `rawFromMathlib B` | At independent section universe `v`, compose `AllOpenMathlib.rawFromMathlib X` with `rawBasisRestriction B`. |
| `fromMathlib B` | At the same independent `v`, compose `AllOpenMathlib.fromMathlib X` with the existing `sheafBasisRestriction B`. Empty normalization and literal sheafhood come from those published constructions. |
| `rawToMathlib B` | At sufficient section universe `max u v`, compose `BasisAllOpen.rawExtension B` with `AllOpenMathlib.rawToMathlib X`. Its values are actual compatible families. |
| `toMathlib B` | At the same sufficient universe, compose `BasisAllOpen.extension B` with `AllOpenMathlib.toMathlib X`. |
| `equivalence B` | Apply `CategoryTheory.Equivalence.trans` to the two actual equivalences. Its forward functor is exactly `toMathlib B`, and its inverse is exactly `fromMathlib B` at section universe `max u v`. |

`rawFromMathlib_obj` identifies the reverse raw object with actual
precomposition by `(basisInclusion B).op`. `fromMathlib_forget` and
`toMathlib_forget` are literal functor equalities with the existing
`sheafForget`, `presheafInclusion`, and `TopCat.Sheaf.forget`. They
identify the action on objects and original natural transformations
together. No parallel source category or sheaf predicate is introduced.
`equivalence_functor` and `equivalence_inverse` expose the specified
forward and reverse functors by reflexivity.

`fromMathlib_sections`, `fromMathlib_restriction`, and
`fromMathlib_map_app` retain the original Mathlib groups
`G.obj.obj (op U.obj)`, maps `G.obj.map (homOfLE h).op`, and actual
morphism components. Their proofs are reflexivity.
`fromMathlib_unique_gluing` applies the published bundled gluing theorem
on these same groups and maps, with an independent arbitrary index
universe `w`. In particular the empty cover remains included.

`toMathlib_sections` identifies the value on every actual open `V` with
`AddCommGrpCat.of (BasisAllOpen.Families F.obj.obj V)`.
`toMathlib_restriction` identifies its underlying additive map with
`BasisAllOpen.familyRestriction`, which discards components outside the
smaller open. `toMathlib_map_app` identifies morphism components with
`BasisAllOpen.familyMap`, which applies each original basis component of
the input natural transformation. These formulas also hold by reflexivity.
The functor laws and sheaf condition are the fields of the actual composed
functors, inherited from the imported constructions.

## Original sections and the composed unit

`basisSectionIso B F U` is the canonical additive equivalence from the
original group `F(U)` to the Mathlib image's value on the same actual
basis open. It is exactly `BasisAllOpen.basisSectionIso F.obj.obj U`.
`basisSectionIso_apply` sends a section to all its original restrictions;
`basisSectionIso_symm_apply` evaluates a compatible family at
`⟨U, le_rfl⟩`. Both inverse laws are the fields of this actual additive
equivalence, proved in the imported construction by restriction identity
and family compatibility.

`basisSectionIso_restriction` intertwines original basis restrictions
with the actual Mathlib restriction maps.
`basisSectionIso_naturality` intertwines every actual input natural
transformation with the composed functor's component. Both reuse the
original componentwise theorems after the literal Mathlib identification.

`unit_hom_apply` and `unit_inv_apply` evaluate the categorical unit of
`equivalence` itself as this displayed additive equivalence and its
inverse. The associators and identity section maps inserted by
`Equivalence.trans` evaluate definitionally to these same maps; the
proofs are reflexivity. Thus the composed categorical comparison still
preserves the given original groups through their canonical additive
isomorphisms.

## Actual gluing and the composed counit

For every actual Mathlib sheaf `G` and actual open `V`,
`counitSectionIso B G V` identifies the extension of its chosen-basis
restriction with the original group `G(V)`. It is exactly the imported
`BasisAllOpen.counitSectionIso` applied to
`(AllOpenMathlib.fromMathlib X).obj G`. The forward map is actual unique
gluing in that sheaf; the inverse is the original chosen-basis restriction
family. Its inverse laws are the fields of the imported additive
equivalence.

`counitSectionIso_symm_apply` evaluates the inverse family at each basis
member as the original Mathlib restriction of the original section.
`counitSectionIso_amalgamation` evaluates gluing on every such member as
precisely the supplied family component. Uniqueness follows from the
imported `BasisAllOpen.counitSectionIso_unique` on the same groups and
maps. `counitSectionIso_restriction` uses the actual Mathlib restriction
maps on all opens, and `counitSectionIso_naturality` uses the actual
Mathlib morphism components. These are the imported theorems under
literal identification of the original groups and maps.

`counit_hom_apply` and `counit_inv_apply` evaluate the categorical counit
of the composed `equivalence` as exactly this gluing equivalence and its
inverse. Their proofs are reflexivity, since the all-open/Mathlib
comparison adds only identity section maps. `functor_triangle` and
`inverse_triangle` expose both coherence laws for these actual composed
functors and categorical unit/counit, using the corresponding fields and
consequence of `Equivalence.trans`.

Empty spaces, empty opens, empty covers, and bases omitting the empty open
are all retained. There is no intersection-closure, Hausdorffness,
local-compactness, total-disconnectedness, countability, metrizability,
nonemptiness, or cover-cardinality assumption. No `HasSheafify`,
sheaf-unit-invertibility, abelianness, or closure certificate is an input.
This module proves no abelianness statement and adds no scalar/module,
stalk, support, or compact-section comparison.

Worker 1153 implemented this comparison layer. Worker 1594 supplied the
actual compatible-family core and published all-open/Mathlib comparison.
Worker 709 supplied the task specification, original-source audit and
universe design. Those existing constructions are reused by Lean name.
