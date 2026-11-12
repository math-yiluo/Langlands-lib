# Geometric connectedness and the remaining smoothness reduction for the chosen dual

For every field `k : Type u`, every abelian scheme `A` over exactly `Spec k`,
and every `hA : HasDualScheme A`, this module proves that the structural
morphism of the existing `dualScheme A hA` is universally closed and
geometrically connected. It also proves properness under an explicit local
finite type hypothesis and reduces the complete
`FieldDualSchemeGeometryStatement.{u}` to the remaining
`FieldDualSchemeSmoothStatement.{u}`.

The module does not prove smoothness or the unconditional full geometry
statement. All fields and schemes stay in universe `u`; no perfection,
projectivity or algebraic closedness hypothesis is added.

## Geometric connectedness under a surjective morphism

`geometricallyConnected_of_surjective` takes schemes `X`, `Y`, `S`,
a surjective morphism `f : X ⟶ Y`, structural morphisms `p : X ⟶ S`
and `q : Y ⟶ S`, and an equality `f ≫ q = p`. It proves that geometric
connectedness of `p` implies geometric connectedness of `q`.

For every field-valued point `y : Spec K ⟶ S` and every pullback `Z` of
`q` along `y`, the pullback of `p` along `y` is connected. Its universal
map to `Z` is a base change of `f`: `IsPullback.of_right` identifies
the left square after pasting the two pullback squares. Surjectivity is
stable under base change. The target `Z` is therefore a continuous
surjective image of a connected space and is connected. This includes
the nonemptiness required by Mathlib's `ConnectedSpace`.

This is descent along a surjective morphism of total spaces, with fixed
base `S`. The published `GeometricallyConnectedDescent` module instead
descends along a surjective change of base.

## The chosen dual

The published unconditional theorem
`Langlands.AbelianScheme.fieldDualSchemeSurjection` supplies an actual
morphism `f : A.X ⟶ dualScheme A hA` in `Over (Spec k)` whose underlying
scheme morphism is surjective. It concerns exactly the existing chosen
parameter scheme and its universal rigidified family.

`fieldDualSchemeUniversallyClosed` uses `Over.w f` to identify the
composite of `f.left` with the dual's structural morphism with `A.X.hom`.
The latter is proper, hence universally closed.
`UniversallyClosed.of_comp_surjective` gives universal closedness of
the dual's structural morphism.

`fieldDualSchemeGeometricallyConnected` applies the preceding
total-space lemma to the same triangle and the geometric connectedness
of `A.X.hom`. It has no local finite type or smoothness premise.

`fieldDualSchemeProper_of_locallyOfFiniteType` supplies separatedness
with the published unconditional theorem
`Langlands.AbelianScheme.fieldDualSchemeSeparated`. Together with the
new universal closedness theorem and the displayed local finite type
instance, Mathlib's `isProper_iff` gives properness.

`FieldDualSchemeGeometryReductionStatement.{u}` is the Prop-valued
definition
`FieldDualSchemeSmoothStatement.{u} → FieldDualSchemeGeometryStatement.{u}`.
It names the conditional reduction and does not assert either statement
unconditionally.

`FieldDualSchemeGeometryStatement.of_smooth` proves this reduction.
It assumes exactly the universe-polymorphic smoothness statement.
For arbitrary `k`, `A`, `hA`,
smoothness gives local finite type; the properness helper and
unconditional geometric connectedness complete the conjunction.
The target statement and its dependency closure are unchanged.

## Provenance and authorship

This is internal derived mathematics using the published exact chosen-dual
surjection and separatedness proofs, the geometric properties of `A`,
and Mathlib's pullback, surjectivity and properness facts. The all-test
rigidified-family comparisons, including nonreduced tests, belong to
the imported proofs; this module preserves their chosen parameter scheme
and adds no comparison with a separately constructed Picard scheme.

The original motivation is the unchanged geometry statement's
Edixhoven, van der Geer and Moonen source, documented in its paired
Markdown. The present module only deduces the conclusions above from
published Library theorems and proves the elementary total-space lemma.

Historical Worker 268 authored the carried surjective-image lemma
and conditional geometry assembly. Worker 858 first supplied published
separatedness, then supplied published surjectivity, extracted the two
unconditional conclusions, and reduced the remaining input to smoothness.
Worker 858 also named the conditional reduction as a Prop-valued statement.
