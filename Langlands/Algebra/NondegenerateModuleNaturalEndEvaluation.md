# Lifted regular evaluation of original forgetful natural endomorphisms

## Source and scope

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Chapter I conventions and I.1.1–I.1.3, printed pp.5–9/PDF11–15, supply the
original nonunital rings, original module actions, fixing idempotents,
nondegenerate full subcategory and compatible right families. I.1.4, printed
p.10/PDF16, distinguishes the right-regular endomorphism model from module
completion on the left. I.1.6, printed pp.11–12/PDF17–18, evaluates a natural
endomorphism of the forgetful functor on the original regular module and uses
naturality for right multiplication to obtain a right-linear additive
endomorphism.

The source displays the forgetful functor with target abelian groups. Its
subsequent proof prose describes an inconsistent target; the implementation
follows the displayed functor, using the actual published
`nondegenerateModuleForgetful` with target `AddCommGrpCat`.

This module constructs that evaluation direction and its intrinsic unital ring
maps. The actual `ULift` carrier, explicit universe enlargement, named additive
and ring structures, conjugation by up/down and complete interface checks are
internal packaging of the source construction. Mutual inverse identities,
injectivity, surjectivity, ring-equivalence classification, topology, closure
and categorical-centre comparisons remain separate obligations.

## Original lifted regular object

Let `A : Type uA` carry its original `NonUnitalRing` structure and let
`hA : IsIdempotented A`. The lifting universe `uM` is independent of `uA`.
`liftedGroup A` names the inherited additive group on `ULift.{uM} A`.
`liftedAction A` is the specified original `NonUnitalModule` action

    a • m = ULift.up (a * m.down).

Its additive and associative laws follow from the original ring laws.
`liftedAction_isNondegenerate hA` applies the published finite two-sided
local-unit characterization to the singleton `{m.down}`; its left-fixing
idempotent fixes `m` after lifting. `liftedRegularObject hA` bundles this group,
this action and this proof as an actual object of
`NondegenerateModuleCat.{uA, max uA uM} A`.

`liftedRegularObject_carrier`, `liftedRegularObject_group` and
`liftedRegularObject_action` identify the entire carrier and selected
structures. `liftedRegularObject_smul` gives the displayed action pointwise.
There is no original unit-action hypothesis.

`rightMultiplication hA b` is an actual endomorphism of this object. Its complete
underlying function, exposed by `rightMultiplication_coe`, is

    m ↦ ULift.up (m.down * b).

`rightMultiplication_hom` identifies its entire additive map with original
`AddMonoidHom.mulRight b` conjugated by the additive up/down equivalence.
`rightMultiplication_apply` supplies point evaluation. Its intertwining field
is proved by the original associativity identity `(a * m.down) * b =
a * (m.down * b)`. Thus this is an original module morphism to which actual
naturality applies.

## Evaluation and right-linearity

For an actual natural transformation
`θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A`, `evaluationEnd hA θ` is
an element of `AddMonoid.End A`. Its entire additive map is

    AddEquiv.ulift.toAddMonoidHom.comp
      ((θ.app (liftedRegularObject hA)).hom.comp
        AddEquiv.ulift.symm.toAddMonoidHom).

Here `AddEquiv.ulift` maps the lifted carrier down to `A`; its inverse maps up.
`evaluationEnd_eq_comp` retains this complete additive composite.
`evaluationEnd_coe` identifies the entire underlying function as

    a ↦ (θ.app (liftedRegularObject hA) (ULift.up a)).down,

and `evaluationEnd_apply` is its point formula.

`evaluationEnd_comp_right` proves equality of the complete additive maps

    (evaluationEnd hA θ).comp (AddMonoidHom.mulRight b) =
      (AddMonoidHom.mulRight b).comp (evaluationEnd hA θ).

The proof uses `θ.naturality (rightMultiplication hA b)`, evaluates that actual
square on `ULift.up a`, and applies `ULift.down`. Additive-map extensionality
then gives the displayed identity. Evaluating it yields
`evaluationEnd_apply_mul`:

    evaluationEnd hA θ (a * b) = evaluationEnd hA θ a * b.

`evaluationRightLinear hA θ` packages this derived equation as an element of
the existing actual subring `IdempotentedRingEndomorphism.RightLinearEnd A`.
Its `val` is exactly `evaluationEnd hA θ`, as stated by
`evaluationRightLinear_val`, and `evaluationRightLinear_apply_mul` restates
the derived right-linearity equation for this subtype value. No
right-linearity certificate is assumed.

## The actual ring homomorphisms

`toEndRingHom hA` is an actual unital ring homomorphism from exactly
`NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A` to `AddMonoid.End A`,
before the codomain is restricted. Its entire function is `evaluationEnd hA`
(`toEndRingHom_coe`, `toEndRingHom_apply`). In the source ring,
`θ * η` has component `(θ.app M).hom.comp (η.app M).hom`, and in
`AddMonoid.End A` a product is also composition with the right factor applied
first. `evaluationEnd_mul` records this orientation as the complete
additive-map identity

    evaluationEnd hA (θ * η) = (evaluationEnd hA θ).comp (evaluationEnd hA η).

`toRightLinearEnd hA` is the actual unital ring homomorphism from the same
named source ring to the existing right-linear endomorphism subring. Both
multiplications apply the right factor first and the left factor second. In
each of these two maps, the zero, addition, unit and multiplication fields
follow by additive-map extensionality (after subtype extensionality for the
subring); after evaluating, they are the inherited component operations and
`ULift.up/down` identities.

`toRightLinearEnd_subtype_comp` states equality of the entire bundled ring map
after the actual subtype inclusion `(rightLinearEnd A).subtype` with
`toEndRingHom hA`, mirroring the published lemma of the same name for the
compatible-family model. `toRightLinearEnd_coe` identifies the entire function
with `evaluationRightLinear hA`. `toRightLinearEnd_val_coe` identifies the
whole map into bundled additive endomorphisms after subtype inclusion with
`evaluationEnd hA`. The application, subtype-value and point formulas are
`toRightLinearEnd_apply`, `toRightLinearEnd_val` and
`toRightLinearEnd_apply_apply`. `toRightLinearEnd_val_apply_mul` is the
naturality-derived right-linearity equation for the image, and
`toRightLinearEnd_mul_apply` gives the multiplication orientation pointwise:

    (toRightLinearEnd hA (θ * η)).val a =
      (toRightLinearEnd hA θ).val ((toRightLinearEnd hA η).val a).

`familyAddHom hA` is precisely the entire additive composite

    IdempotentedRingEndomorphism.idempotentEvaluation.comp
      (toRightLinearEnd hA).toAddMonoidHom.

It uses the published actual `idempotentEvaluation`, which sends a right-linear
endomorphism `T` to the compatible right family `e ↦ T e`. Right-linearity
ensures `T(e) * e = T(e)` and `T(f) * e = T(e)` whenever `e ≤ f`; this supplies
the existing right-family compatibility, with no classification premise.
`familyAddHom_eq_comp` states equality of the whole additive composite, and
`familyAddHom_coe` gives its entire function.
`familyAddHom_val_coe` identifies its complete coordinate function with

    e ↦ (θ.app (liftedRegularObject hA) (ULift.up (e : A))).down.

`familyAddHom_val` gives the corresponding point identity.

`familyAddHom_one` proves agreement with the published family unit by
coordinate extensionality. To prove `familyAddHom_mul`, fix an idempotent `e`
and choose a left local unit `f` for `evaluationEnd hA η e`. The published
`product_val` computes the product coordinate as

    evaluationEnd hA θ f * evaluationEnd hA η e.

Right-linearity and `f * evaluationEnd hA η e = evaluationEnd hA η e` identify
this expression with
`evaluationEnd hA θ (evaluationEnd hA η e)`, exactly the evaluation of `θ * η`.
This proves the family product law directly from its actual formula.

`toFamilyRingHom hA` installs exactly the named natural-endomorphism source
ring and `IdempotentedRingRightLimit.ring hA`. Its function is `familyAddHom hA`;
its additive laws come from that additive map, and its unit and product laws
are the preceding intrinsic proofs. `toFamilyRingHom_coe` is the complete
function identity. `toFamilyRingHom_toAddMonoidHom` identifies the entire
additive projection with the stated `idempotentEvaluation` composite, selecting
both named rings in its type. `toFamilyRingHom_val_coe` and
`toFamilyRingHom_val` retain the complete coordinate function and every point
evaluation.

## Universes and structure selection

The actual regular carrier need not belong to an independently selected
smaller module universe. The present construction evaluates in the category
at module universe `max uA uM`, where `ULift.{uM} A` is available. It makes no
downward transfer to arbitrary smaller module-carrier universes. In particular,
the check with `(uA,uM) = (1,0)` still uses carrier universe `max 1 0 = 1`.

Three blocks assign unapplied declarations to their complete expected
outer telescopes: arbitrary independent `uA,uM`, `(0,1)` and `(1,0)`.
They cover the lifted group/action and nondegeneracy, actual object and chosen
structures, actual right multiplication and its full additive map/function,
evaluation and its full additive composite/function, naturality-derived
right-linearity, the actual subtype, the unrestricted ring map and its
function, the multiplication orientation, the right-linear ring map with its
subtype-inclusion identity, the whole family additive composite/function and
the family ring map with its entire additive projection and coordinate
function. Each occurrence fixes the lifting universe explicitly;
the reduced maximum alone would not recover it in the `(1,0)` case.

`CompetingOriginalRings` passes the specified original scalar ring explicitly
while another original ring structure is available on the same type; the
carrier, group, action, original multiplication and complete evaluation
function retain that choice. `CompetingLiftedStructures` supplies competing
additive-group and action instances on the very same lifted carrier and checks
the named group/action and complete right-multiplication additive map.
`CompetingEndAndFamilyRings` places competing source and family ring instances
in scope while verifying both ring maps, the subtype-inclusion identity, the
pointwise right-linear multiplication orientation, the complete additive
composite, the actual family multiplication law and full coordinate function
with the named rings installed. Each of these checks is closed by a declaration
whose type uses the named rings, so it fails if a competing instance is
selected.

`SubsingletonRing` checks the actual lifted action on a subsingleton carrier
and constructs `IsIdempotented A` using the zero idempotent. For every actual
natural endomorphism it proves that the entire evaluated additive map and
family image are zero by extensionality. Thus zero rings and their lifted
subsingleton additive carriers are included. The construction assumes no
commutativity, nontriviality, finite dimension, original unit-action or `Small`
condition, and uses no inverse or classification theorem.
