# Actual forgetful natural-endomorphism classification statements

This module declares propositions for Renard I.1.6. It supplies no proof of a
classification assertion. All eight constituent assertions and their aggregate
`NondegenerateModuleNaturalEndClassificationStatement.Classification` remain
proof obligations.

## Source and provenance

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Chapter I conventions and I.1.1–I.1.3, printed pp.5–9/PDF11–15, specify the
original nonunital rings, module actions, local units, nondegenerate objects,
compatible right families and their extended action. The closing remark of
I.1.4, printed p.10/PDF16, notes that I.1.3 completed `A` as a right module
over itself and identifies the completed ring with `End_{A°}(A)`. The
proposition and final proof paragraph of I.1.6, printed
pp.11–12/PDF17–18, identify the completed ring with endomorphisms of the
forgetful functor and assert that evaluation and extended action are inverse.

The displayed forgetful functor has target abelian groups, denoted
`Z-mod` in the conventions. The subsequent proof prose instead describes
functors from the nondegenerate category to itself, an inconsistent target.
These statements follow the displayed functor, implemented by the actual
`nondegenerateModuleForgetful` with target `AddCommGrpCat`.

The explicit `ULift` carrier, enlarged universe, named ring structures, bundled
ring-map identities, full additive-component identities and specified
ring-equivalence functions are internal packaging of the source assertion.
The component and coordinate recovery statements spell out the source's
mutual-inverse assertion. They are conclusions to prove; they are not assumed
certificates or hypotheses on replacement constructions.

## The actual maps and structures

Let `A : Type uA` have its original `NonUnitalRing` structure and let
`hA : IsIdempotented A`. The lifting universe `uM` is independent of `uA`.
Write

    R = IdempotentedRingRightLimit A
    T = NondegenerateModuleNaturalEnd.{uA, max uA uM} A.

`R` is the published compatible-right-family carrier: `x.val e` lies in
`A e`, and `x.val f * e = x.val e` whenever `e ≤ f`. Its ring is exactly
`IdempotentedRingRightLimit.ring hA`. `T` consists of actual natural
transformations of the original forgetful functor. Its ring is exactly
`NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A`, the inherited
categorical endomorphism ring.

The two maps in every declaration are

    F = IdempotentedRingRightLimit.toNaturalEndRingHom.{uA, max uA uM} hA
    G = NondegenerateModuleNaturalEndEvaluation.toFamilyRingHom.{uA,uM} hA.

For each actual nondegenerate original object `M`, the entire additive
component of `F x` is the published `actionAddHom hA M.property x`.
At an element `m` fixed by an idempotent `e`, this map sends `m` to
`x.val e • m`.

`G` evaluates the actual additive component on
`NondegenerateModuleNaturalEndEvaluation.liftedRegularObject.{uA,uM} hA`,
whose carrier is `ULift.{uM} A` and whose original action is
`a • m = ULift.up (a * m.down)`. It conjugates by the actual up/down
additive equivalence, derives right-linearity from naturality for actual
right multiplication, and applies the published `idempotentEvaluation`.
Consequently its coordinate formula is

    (G θ).val e =
      (θ.app (liftedRegularObject hA) (ULift.up (e : A))).down.

Both ring multiplications apply the right factor first and then the left
factor: `(θ * η).app M` has additive map
`(θ.app M).hom.comp (η.app M).hom`. The family product extends the same
composition orientation. There is no opposite multiplication in these
statements.

## Constituent propositions

Each constituent is a `def` returning `Prop`, with only the original ring,
`hA` and the two independent universe parameters.

* `FamilyCompositeIdentity hA` states the equality of entire bundled maps
  `G.comp F = RingHom.id R`, installing both named rings.
* `NaturalEndCompositeIdentity hA` states the equality of entire bundled maps
  `F.comp G = RingHom.id T`, with the same named rings.
* `FamilyRecovery hA` states `G (F x) = x` for every actual compatible family.
* `NaturalEndRecovery hA` states `F (G θ) = θ` for every actual natural
  transformation.
* `ComponentRecovery hA` states
  `((F (G θ)).app M).hom = (θ.app M).hom` for every actual `θ` and every
  `M : NondegenerateModuleCat.{uA, max uA uM} A`. These are entire
  additive maps obtained by the actual `AddCommGrpCat` morphism projection.
* `ComponentPointRecovery hA` states `(F (G θ)).app M m = θ.app M m`
  for every such `θ`, `M` and `m : M.obj`.
* `CoordinateRecovery hA` states `(G (F x)).val e = x.val e` for every
  actual family `x` and every original `e : Idempotent A`.
* `SpecifiedRingEquivalence hA` states existence of an actual `E : R ≃+* T`
  with equality of the entire forward function `(E : R → T)` to `F`
  and equality of the entire inverse function `(E.symm : T → R)` to `G`.
  Both named rings are selected in the equivalence type.

`Classification.{uA,uM}` universally quantifies the type `A`, its original
ring structure and `hA`, and conjoins these eight propositions in the order
above. It assumes no inverse or reconstruction assertion. No equivalence,
bijectivity, topology or regular-object reconstruction is supplied as a
premise.

## Universes and interface checks

The module-carrier universe is explicitly `max uA uM`, so the specified
lifted original regular object belongs to the category. An original ring
carrier need not belong to an arbitrarily smaller independently chosen
module universe. No downward universe transfer is asserted. In particular,
the assignment `(uA,uM) = (1,0)` still uses module-carrier universe 1.

The source checks assign every entire unapplied constituent declaration to
its expected telescope and the unapplied aggregate to `Prop`, first at
arbitrary independent universes and then at `(0,1)` and `(1,0)`.
`CompetingOriginalRings` explicitly selects a named original scalar ring
while another ring structure is in scope and identifies each of the eight
constituent propositions with its formula. `CompetingEndAndFamilyRings`
places competing source and target ring instances in scope. In addition to
the formulas with local instances, it checks both whole maps at explicit
`@RingHom` types whose semiring arguments are the projections of the named
rings. It identifies both entire ring-map-identity propositions with
explicit `@RingHom.comp` and `@RingHom.id` formulas, both pointwise
recoveries with explicit `@DFunLike.coe` applications through
`@RingHom.instFunLike` at the named semirings, and the
specified-equivalence proposition with an explicit `@RingEquiv` using the
named multiplication and addition. The `ZeroRings` section takes an
arbitrary original ring with `[Subsingleton A]` and checks that the
aggregate specializes there, with the ambient original ring, to the
conjunction of the eight constituents.

Lean may elaborate the natural-endomorphism semiring argument through the
global categorical endomorphism instance rather than through the local
named `Ring` instance. These are definitionally the same inherited
operations. The checks establish compatibility with the explicitly named
operations; they do not claim which instance-search route wins. They are
definitional interface checks, not proofs of the declared classification
assertions.

Arbitrary noncommutative and nonunital rings, including zero rings, remain
within the quantifiers. There is no `Nontrivial`, original unit-action,
finite-dimensionality or `Small` assumption. Topology, closure, categorical
centres, arbitrary smaller carrier universes and the separately owned
right-linear comparison results are outside this statement unit.
