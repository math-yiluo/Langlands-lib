# The actual nondegenerate-module centre and the original commutant action

This module constructs three things: the categorical centre of the actual category
of original nondegenerate modules, its faithful forgetful ring map, and the forward
action of the original-image commutant in the compatible-right-family ring. The
carrier is the abbreviation `Langlands.Algebra.NondegenerateModuleCenter`. All
other declarations are in the namespace of the same name.

Authors: Worker 6 designed and wrote the first complete version of the module and
this note. Worker 751 audited it against the task and the source. Worker 751 then
gave the ring-map declarations explicit named ring structures, added the
multiplication-orientation, composite-component and compatibility checks, and
revised this note. Worker 1126 audited the draft and supplied several checks that
were adopted: the instance-compatibility `rfl` examples, the family-component
formula, the component product formula, the existential zero-ring example and the
missing interface checks.

## Source and provenance

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The relevant passage is I.1.7: its lemma and the prose and theorem that follow,
printed pp.12–13 / PDF pp.18–19. The conventions and I.1.1–I.1.6, printed
pp.5–12 / PDF pp.11–18, fix the original nonunital rings, original module
actions, nondegeneracy and the compatible right families. In particular, I.1.3
completes the ring as a right module over itself, and the final remark of I.1.4
identifies this completion with the right-linear endomorphisms of the original
ring.

The I.1.7 lemma starts from a right-linear endomorphism `φ` that also commutes
with left multiplication, `φ(abc) = a φ(b) c`. On a nondegenerate module it acts
on `m` by choosing an idempotent `e` with `e · m = m` and applying `φ(e)` to `m`.
It proves `φ̃_M(a · m) = φ(a) · m` and states naturality in original module
morphisms. The following prose says that such `φ` give natural transformations
of the identity functor, and the theorem identifies the centre of the category
with this commutant. The source also says that the centre has a ring structure.
The construction here reuses the published compatible-family action of
`Langlands.Algebra.NondegenerateModuleForgetful`. It derives original scalar
linearity from commutation with the canonical original-ring image.

The actual `CatCenter`, the actual `Subring.centralizer`, the named inherited
rings, the bundled ring maps, the faithful forgetful map and the whole-map
identities are internal packaging of that source construction. The proofs below
establish the intrinsic laws of this packaging. They do not assume the inverse or
classification assertions of the I.1.7 prose and theorem.

## Hypotheses, universes and operations

Let `A : Type uA` carry its original `NonUnitalRing` structure. Its multiplication
may be noncommutative; no unit or nontriviality is required. Original modules use
the published `NonUnitalModule`, which imposes no unit-action law even when the
original ring happens to have a unit. Nondegeneracy says that each module element
is fixed by an original idempotent.

The module-carrier universe `uM` is independent of `uA`.
`NondegenerateModuleCenter.{uA,uM} A` is definitionally
`CatCenter (NondegenerateModuleCat.{uA,uM} A)`, in `Type (max uA (uM + 1))`.
Its components are actual original module intertwiners. The named `ring` is the
inherited ring of natural endomorphisms of the identity functor on this
preadditive category, and `carrier_eq` identifies the actual carrier.
`mul_app_toAddMonoidHom` is stated for the product of the named `ring`, written
explicitly. It is an equality of entire additive components: the component of
`z * w` is the additive map of `z` composed with that of `w`. Thus the right
factor acts first.

The centre and its forgetful map need no `IsIdempotented` argument. The commutant
and its action also take `hA : IsIdempotented A`, which supplies the local units
used in the published family ring and its module actions. No regular object,
`Small`, universe inequality or classification hypothesis is used.

## Faithful forgetful map

`forget` applies the actual `nondegenerateModuleForgetful` to each original
intertwiner component, giving an element of
`NondegenerateModuleNaturalEnd.{uA,uM} A`. Its naturality comes from applying the
functor to the original naturality equation. `forgetRingHom` bundles this as a
unital ring homomorphism. Its declared type is `@RingHom` with source
`(ring A).toNonAssocSemiring` and target
`(NondegenerateModuleNaturalEnd.ring A).toNonAssocSemiring`, both written
explicitly. The four preservation laws hold componentwise by the inherited
operations.

`forgetRingHom_coe` fixes the entire underlying function as `forget`.
`forget_app_hom` identifies the entire additive component with the original
component's `toAddMonoidHom`. `forget_app_coe` fixes its underlying function, and
`forget_app_apply` gives the pointwise version. `forgetRingHom_injective` uses
centre extensionality, full-subcategory morphism extensionality and original
module-homomorphism extensionality. It needs no evaluation at the regular module.

## Actual original-image commutant

With exactly the ambient `IdempotentedRingRightLimit.ring hA`,
`commutantSubring hA` is

```text
Subring.centralizer (Set.range (IdempotentedRingRightLimit.canonicalRingHom hA)).
```

Here the canonical map retains the original nonunital ring structure on `A`.
`Commutant hA : Type uA` is the actual subtype of this subring, and
`commutantRing hA` is its named inherited ring. `commutantSubring_eq` records the
entire subring equality. `commutantInclusion` is the actual subring inclusion
`(commutantSubring hA).subtype`. Its declared type is `@RingHom` from
`(commutantRing hA).toNonAssocSemiring` to
`(IdempotentedRingRightLimit.ring hA).toNonAssocSemiring`.
`commutantInclusion_coe` identifies its whole function with `Subtype.val`.

`mem_commutantSubring_iff` says that membership is equivalent to
`canonical a * x = x * canonical a` for every original `a : A`.
`commutes` states the same equation with the published explicit `product`.
These are properties of the actual centralizer subtype, not extra supplied
reconstruction data.

## Forward action and intrinsic proofs

For `x : Commutant hA` and an actual nondegenerate module `M`, `action_smul`
proves original `A`-linearity of
`IdempotentedRingRightLimit.actionAddHom hA M.property x.val`.
The proof acts on `m` with both sides of `canonical a * x = x * canonical a`, then
applies the published product-action and canonical-action laws. This gives
`act x (a • m) = a • act x m`.

`component hA x M` bundles this entire additive action as an original
`NonUnitalModuleHom A M.obj M.obj`. `component_toAddMonoidHom`, `component_coe`
and `component_apply` identify its entire additive map, its entire underlying
function and its value. `component_eq` is the source's fixing-idempotent formula:

```text
component hA x M m = x.val.val e • m     if (e : A) • m = m.
```

`action_original_smul` proves, for every compatible family `y`, even before
imposing commutation,

```text
actionAddHom hA M.property y (a • m) = applyOriginal hA y a • m.
```

This is the source lemma's formula `φ̃_M(a · m) = φ(a) · m`. The proof chooses a
local left unit `e` for `a` from the two-sided local units of `hA`; it then also
fixes `a • m`. The published fixing-idempotent formula and `applyOriginal_eq`,
followed by original module associativity, give the result. The source instead
takes idempotents fixing `a · m` and `a` and a common upper bound of the two. The
proofs differ, but the statement is the same. `component_original_smul` specializes this to the
actual commutant component. `component_mul_toAddMonoidHom` says that the
component of a product, taken in the named `commutantRing`, is the composite with
the right factor's component applied first. It follows from the published
`actionAddHom_product`.

`commutantCenter` has `component hA x M` as its original intertwiner at `M`. Its
naturality follows from the published equality of entire additive maps
`actionAddHom_naturality`, evaluated on each element. The equality is reversed to
match the categorical composition convention. `commutantCenter_app_hom` fixes the
entire original component. `forget_commutantCenter` identifies the entire
forgotten natural transformation with
`IdempotentedRingRightLimit.familyNaturalEnd hA x.val`.

`fromCommutantRingHom` bundles `commutantCenter` as a unital ring map. Its
declared type is `@RingHom` from `(commutantRing hA).toNonAssocSemiring` to
`(ring A).toNonAssocSemiring`. Its zero, unit, addition and multiplication laws
follow from the corresponding published family laws, via the proved injectivity
of `forgetRingHom`. No classification is assumed. `fromCommutantRingHom_coe`
fixes the entire underlying function. The `fromCommutantRingHom_app_*`
declarations fix four things: the entire additive component and its function,
its value at each element, its fixing-idempotent value and its value at `a • m`.
`fromCommutantRingHom_mul_app_toAddMonoidHom` keeps the right-factor-first
orientation explicit. The component of the image of a named-commutant product
`x * y` is `actionAddHom x.val` composed after `actionAddHom y.val`.

Finally, `forgetRingHom_comp_fromCommutantRingHom` is an equality of entire
bundled ring homomorphisms. All four ring structures are written explicitly in
`@RingHom.comp`:

```text
forgetRingHom.comp (fromCommutantRingHom hA)
  = (IdempotentedRingRightLimit.toNaturalEndRingHom hA).comp
      (commutantInclusion hA).
```

It holds by `rfl`, because both sides have exactly the published family action
as their components. Two component formulas accompany the whole-map equality.
`forget_fromCommutantRingHom_app_hom` says that the component at `M` of the
forgotten image of `x` is `actionAddHom hA M.property x.val`.
`forget_fromCommutantRingHom_app_hom_eq_family` says that it equals the component
at `M` of `toNaturalEndRingHom hA (commutantInclusion hA x)`.

## Named structures and the inherited instance

The declared types of `forgetRingHom`, `commutantInclusion`,
`fromCommutantRingHom`, the composite equality and the two multiplication
formulas write the named structures explicitly. Their interfaces therefore do not
depend on which instance a typeclass search returns.

The named rings are definitionally compatible with the inherited instances.
`rfl` examples check four facts:

- `ring A` equals the `Ring` instance that instance search returns for
  `CatCenter (NondegenerateModuleCat A)` and for `End (𝟭 _)`, which comes from
  Mathlib's inherited categorical endomorphism instances.
- `commutantRing hA` equals `Subring.toRing` of the actual `commutantSubring hA`
  in `IdempotentedRingRightLimit.ring hA`, and equals the instance found once
  that ambient ring is introduced locally.
- The function of `commutantInclusion hA` is that of `(commutantSubring hA).subtype`.
- In the named `ring`, `z * w = w ≫ z`, `z + w` is the inherited sum, `1` is
  `𝟙 (𝟭 _)` and `0` is the inherited zero.

These checks compare structures and make no claim about which typeclass-search
route is chosen. A further example obtains `IsMulCommutative` for the centre from
Mathlib's inherited instance. It is a check only; this module states no
commutativity lemma of its own.

## Interface checks and scope

The final Lean examples check complete unapplied declaration types for the
principal carriers, named rings, actual commutant, inclusion, component, forgetful
map, forward ring map, multiplication formulas and whole-map and component
identities. They are checked at arbitrary independent universes and at both
`(uA,uM) = (0,1)` and `(1,0)`. The forward construction stays at `uM` itself.

Further examples supply a competing original ring, competing `Ring` instances on
the family ring, the commutant, the centre and the forgetful endomorphism ring,
and a competing original module action on the same carrier. The examples are
typed with explicitly named expected `RingHom` structures and explicit
original-action projections. They check that the declarations use the original
ring, the named rings and the original action, not the competing ones.

Under `[Subsingleton A]`, one example constructs an `IsIdempotented A`
witness. For that witness, it proves that every commutant component on every
nondegenerate module has zero additive map. A second example proves the same for
the components of `fromCommutantRingHom`, for any given `hA`. So zero rings are
covered.

This module does not construct evaluation from the categorical centre or prove
mutual inverses or classification. It does not identify this original-image
commutant with the centre of the entire family ring or with the limit of corner
centres. Topology, closure, the unital-specialization comparison and I.1.8
remain separate obligations.
