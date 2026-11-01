# Original forgetful functors and canonical natural endomorphisms

This definition unit implements the forward construction in David
Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, I.1.6, printed pages 11–12/PDF17–18. The registered
source is `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The conventions and original module categories come from Chapter I
conventions and I.1.1–I.1.2, printed pages 5–8/PDF11–14; the action being
packaged was constructed from I.1.3, printed page 9/PDF15.

## Actual functors

`nonUnitalModuleForgetful A` sends an original ambient module to
`AddCommGrpCat.of M`, retaining its specified additive group, and an original
intertwiner to `AddCommGrpCat.ofHom f.toAddMonoidHom`. It retains the entire
additive map, including on degenerate ambient modules and zero actions.
Its identity, composition and addition laws are definitional equalities.
The object, carrier, entire morphism, entire underlying additive map and
point-evaluation lemmas expose these choices.

`nondegenerateModuleForgetful A` is literally the published full inclusion
`nondegenerateInclusion A` followed by that ambient functor. The object has
the same original additive carrier `M.obj`; the map is exactly the additive
map of `f.hom`. Its additivity is inherited from the published inclusion and
the ambient functor. `AddCommGrpCat` is the standard category of abelian
groups used to model the source's `ℤ-mod`. The proof on PDF18 describes
the surrounding functor category as having target `M(A)`; the displayed
forgetful functor on PDF17 has target `ℤ-mod`, and that displayed target is
used here.

## Actual natural-endomorphism ring

`NondegenerateModuleNaturalEnd A` abbreviates
`CategoryTheory.End (nondegenerateModuleForgetful A)`. Its elements are the
actual natural transformations of the actual functor category. The imported
Mathlib preadditive functor category and categorical endomorphism ring give
its ring structure. `NondegenerateModuleNaturalEnd.ring A` names exactly
that inherited ring, so the bundled forward map can specify it even when
an unrelated ring on the same carrier is in scope.
The component additive maps of zero, addition, one and
multiplication are exposed. In particular,
`(θ * η).app M` has additive map `(θ.app M).hom.comp (η.app M).hom`:
the left factor acts after the right factor.

## Forward family map

`IdempotentedRingRightLimit.actionAddHom hA hM x` bundles the published
`IdempotentedRingRightLimitAction.act hM x` as an additive endomorphism of
the original module. The zero and addition laws in the vector argument
come from the published action laws, without changing the original action
or additive group. Its entire function is that action.
`actionAddHom_eq` evaluates it at every fixing idempotent:
if `e • m = m`, the result is `x.val e • m`.
`actionAddHom_canonical` identifies the entire additive map of a canonical
family with `NonUnitalModule.toEndHom` for the specified original action.

The zero, addition, unit and product identities in the family argument are
equalities of entire additive maps. Their proofs use additive-map
extensionality and the corresponding published action identities.
`actionAddHom_naturality` is equality of the two entire composed additive
maps for an original intertwiner between independently sized modules.
It follows pointwise from the published `map_act`.

`familyNaturalEnd hA x` has component
`AddCommGrpCat.ofHom (actionAddHom hA M.property x)`.
Its naturality is the symmetry of that complete additive-map identity,
because categorical composition writes the first map on the left.
Natural-transformation extensionality and the component identities prove
its zero, addition, unit and product laws.

`toNaturalEndRingHom hA` bundles precisely that function as a unital ring
homomorphism, installing exactly the published
`IdempotentedRingRightLimit.ring hA` on its source and
`NondegenerateModuleNaturalEnd.ring A` on its target. The full-function,
component, full-additive-component, full-component-function and evaluation
lemmas expose every bundling. At a fixing idempotent its value is `x(e) • m`;
at the canonical family of `a` it is the original action `a • m`, including
equality of the entire original additive endomorphism.

## Scope and universes

The scalar carrier is `Type uA` and each bundled functor fixes the
independent original module-carrier universe `Type uM`. The unbundled
component and naturality also allow independently sized source and target
module carriers `Type uM` and `Type uN`. The actual natural-endomorphism
type lives in `Type (max uA (uM + 1))`: natural transformations quantify
over all objects of the original bundled module category. The family
carrier remains in `Type uA`. No size assumption relates `uA` and `uM`, and no regular
object is used. No identity in the original ring, nontriviality,
commutativity, countability or dimension assumption is added.

The ambient extension, explicit additive maps and categorical ring are
internal packaging of Renard's forgetful functor and forward action
construction. This unit establishes no injectivity, surjectivity, inverse,
classification, topology, closure or centre theorem. Recovering an element
from a natural transformation by evaluation at the regular module requires
that object to fit in the source category's carrier universe and belongs
to a separate audited statement/proof unit.

## Interface checks

The final examples assign the unapplied principal constructions, object
and carrier formulas, full morphism and additive-map formulas, the named
inherited ring, multiplication orientation, complete naturality equation,
full forward function, component functions, fixing-idempotent and canonical
action formulas to their full expected telescopes. They retain arbitrary
independent universes and also specialize the same telescopes at
`(uA,uM,uN) = (0,1,0)` and `(1,0,1)`.

Competing-ring examples put unrelated rings on both the family carrier and
the natural-endomorphism carrier in scope. The expected bundled map
explicitly selects the published source ring and named inherited target
ring, and its complete function, component and action formulas remain the
specified ones. Competing-action examples put an unrelated action on the
same original additive carrier in scope, explicitly pass the original
action to the unbundled component and its formulas, and verify the same
original component after bundling the module. An intertwiner between the
two actions retains its entire additive map under the ambient functor.

The original scalar carrier itself is also tested with the zero action.
For an arbitrary subsingleton additive group, the zero idempotent supplies
nondegeneracy and additive-map extensionality gives zero components. For a
subsingleton scalar ring, the examples construct local units from the zero
idempotent, use a fixing idempotent for each vector and then the coordinate
formula and original zero-scalar law to prove every component is zero.
These examples impose no nontriviality or original unit-action law.
