# Coherent associated-system comparison along varying group and cover maps

Author: Worker 57.

This internal construction compares complete associated sheaf systems when
both the finite residual groups and their covers change. An actual natural
group map restricts the actions without changing the underlying coefficient
functor. An actual equivariant natural map of covers then gives a natural
isomorphism of whole associated-system functors, under the finite geometric
torsor properties of the two original cover actions.

## Restriction of the complete equivariant diagram

`Langlands.EquivariantDiagram.groupRestriction` has inputs an index
category `I : Type uI` with `Category.{vI} I`, group diagrams
`D E : I ⥤ GrpCat.{u}`, a natural transformation `φ : D ⟶ E`, and a
category `C : Type uC` with `Category.{vC} C`. It constructs the functor

```text
EquivariantDiagram E C ⥤ EquivariantDiagram D C.
```

For `M` over `E`, its complete underlying diagram is exactly `M.obj`,
including every transition. At `i`, its action is
`(M.ρ i).comp (φ.app i).hom`. Applying the original transition
equivariance to `φ_i(g)` and then evaluating the naturality equation of
`φ` on `g` proves the required equivariance for `D` transitions.

On an equivariant diagram morphism `c`, the underlying natural
transformation is exactly `c.hom`. Its equivariance is the original
`c.comm i (φ_i(g))`. Extensionality and reflexivity prove identity and
composition. The `obj_obj`, `obj_action` and `map_hom` normalizations
identify the full retained functor, its action as the original
`Action.res` action, and each retained morphism by reflexivity.

The object and morphism universes of `I` and `C` are independent. The
two group diagrams share the group universe `u`; this unit does not
change their carriers to a different universe.

## Actual cover-map and coefficient inputs

The remaining declarations are in
`Langlands.Shimura.Coefficients`. Fix `X : Scheme.{u}`, a commutative
ring `R : Type u`, and the same index category, group diagrams and
natural group map. Write `J = X.smallEtaleTopology`.

The cover inputs are

```text
Y : EquivariantDiagram D X.Etale
Z : EquivariantDiagram E X.Etale
a : Y ⟶ (EquivariantDiagram.groupRestriction X.Etale φ).obj Z.
```

Consequently `a.hom` is an actual natural transformation from the full
underlying `Y` diagram to the full underlying `Z` diagram. At `i`,
its component is equivariant from `Y.action i` to the original
`Z.action i` restricted along `φ_i : D_i →* E_i`. Both its index
naturality and its component equivariance are part of this actual
cover-diagram morphism.

Let `M : EquivariantDiagram E (ModuleCat.{u} R)`, and write `resφ M`
for the group restriction just constructed. Its module functor,
module maps and scalar ring are unchanged. No finiteness, freeness,
local-constancy or invertibility condition on coefficients or their
transitions is added.

## Component comparison and its section formula

`etaleAssociatedAtGroupCoverChange X R φ Y Z a i` is the natural
transformation

```text
etaleAssociatedAt X Z i ⟶
  groupRestriction (ModuleCat R) φ ⋙ etaleAssociatedAt X Y i.
```

It is the existing `etaleAssociatedCoverChange` at the actual action
map `a_i`, whiskered with evaluation of the original coefficient
diagram at `i`. Thus its component `q_i(M)` is exactly

```text
etaleCrossCoverMap X φ_i a_i (𝟙 (Action.res φ_i M_i)).
```

The `app` theorem identifies this original cross-cover map by
reflexivity. The coefficient map is the identity on the restricted
original coefficient action. No cover isomorphism is assumed.

The `inclusion` theorem applies
`etaleCrossCoverMap_identity_inclusion` to these exact cover actions.
If `e^Z_i(M)` and `e^Y_i(resφ M)` are the invariant-section inclusions,
it gives

\[
 q_i(M)\,;\,e^Y_i(res_\varphi M)
   =e^Z_i(M)\,;\,\operatorname{cp}(a_i,M_i).
\]

Here `cp` is the existing `coverPullback` on the actual underlying
small-etale cover map. This formula retains the coefficient vector and
pulls only the cover coordinate. The component construction and this
identity do not require torsor premises.

## Whole-system coherence and invertibility

Now assume

```text
hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i)
hZ : ∀ i, IsFiniteGeometricTorsor X (Z.action i).
```

These premises concern each of the two original group actions. The unit
does not assert that restriction of the `E_i` torsor action to `D_i`
is itself a geometric torsor. No additional injectivity or surjectivity
premise on `φ_i` is required by the existing comparison theorem.

`etaleAssociatedAtGroupCoverChange_isIso` applies
`etaleAssociatedCoverComparison` to the two original finite geometric
torsors, the actual group homomorphism `φ_i` and the equivariant cover
map `a_i`. It proves invertibility of the same `q_i(M)`.

Write `L_Z(M)` and `L_Y(resφ M)` for the existing full associated systems.
For every index arrow `f : i → j`,
`etaleAssociatedAtGroupCoverChange_transition` proves

\[
 L_Z(M)(f)\,;\,q_j(M)
   =q_i(M)\,;\,L_Y(res_\varphi M)(f).
\]

The implemented proof uses
`etaleAssociatedTransition_hom_ext` for the target system. The section
formula above rewrites the two component comparisons. The original
`etaleAssociatedTransition_inclusion` formulas rewrite both system
transitions. Naturality of `a.hom` and contravariant composition of
`coverPullback` identify the two cover pullback composites.
Finally coefficient naturality of `coverPullback`, together with the
unchanged underlying coefficient transitions of `resφ M`, gives the
required equality. Desired transition coherence is proved from these
maps, not supplied as a premise.

The entry definition `etaleAssociatedVaryingGroupCoverIso` constructs
the natural isomorphism

```text
etaleAssociatedVaryingSystemFunctor X Z hZ ≅
  groupRestriction (ModuleCat R) φ ⋙
    etaleAssociatedVaryingSystemFunctor X Y hY.
```

For each coefficient diagram, `NatIso.ofComponents` uses the proved
component invertibility and index-transition equation to construct the
whole-system isomorphism. Another `NatIso.ofComponents` assembles these
in the original coefficient diagram. Its naturality is exactly the
coefficient naturality of the component cross-cover comparison.

The `hom_app` theorem identifies each component of its forward map
with `q_i(M)` by reflexivity. The `inv_transition` theorem is naturality
of its actual inverse whole-system map, so it also retains every
original index transition.

## Provenance and use in the CM constructions

This is an internal deduction from the direct import
`VaryingSystemCoverChange`, its original cross-cover and associated
system constructions, and the actual `EquivariantDiagram` category.
Precomposing actions along a natural group map constructs restriction.
The existing cross-cover functor constructs the component comparisons;
the original invariant-section identities and actual cover-map
naturality prove whole-system coherence; the existing finite geometric
torsor comparison proves invertibility. No additional external-source
assertion is introduced.

The existing fixed-group whole-system cover change uses the identity
group homomorphisms. This unit admits a natural map between two
different group diagrams and keeps coefficient restriction explicit,
as needed for actual CM common-kernel quotient maps. It does not
construct the CM levels or covers: those are supplied by the separate
arithmetic and geometric CM constructions, which can instantiate this
generic result. Compatibility under further composition of changing
group diagrams, inverse image across base schemes, and full geometric
CM level coherence remain separate constructions.
