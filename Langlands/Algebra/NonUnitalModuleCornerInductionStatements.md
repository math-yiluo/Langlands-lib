# The actual fixed-part induction isomorphism: statements

This module states the natural isomorphism in David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, I.3.2, formula (I.3.2.1), printed page 20 / PDF page 26.
The displayed map is `z ↦ e ⊗ z` from a unital `eAe`-module to the
`e`-fixed part of its actual induced module. The principal declarations are
closed, unproved `Prop` definitions. This contribution supplies statement
coverage and small intrinsic typing helpers. Worker 1155 implemented the
statements; Worker 6 supplied the mathematical interface specification and
preliminary universe and named-instance audit.

## Sources and internal strengthening

The governing source is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
The author read Chapter I conventions, printed pages 5–7 / PDF pages
11–13; I.2.1–I.2.2, printed pages 14–16 / PDF pages 20–22; and
I.3.1–I.3.2, printed pages 19–20 / PDF pages 25–26.

The supplementary registered `renard-2010-corrections-complements`,
SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read at PDF pages 1–2. Its warning that the right corner action on
`A` need not be unital and its corrected injectivity argument are already
incorporated in the governing 2026 passage. The 2010 supplement does not
replace the 2026 text.

Renard's I.3 setting is a complex algebra with local idempotent units.
The pointwise and ambient categorical targets here state an internal
additive strengthening: `A` is any associative, possibly noncommutative
`NonUnitalRing`; `e` is any actual idempotent; and `Z` is an arbitrary
additive group with an ordinary unital module structure over the actual
`Idempotent.Corner e`. No complex action, commutativity, nontriviality,
faithfulness, dimension restriction or local-unit condition is assumed
for these targets. The sandwich formula and tensor balancing motivate
this strengthening; their presence in a statement is not a proof of it.
The separate source-category adapter assumes `IsIdempotented A` solely
to use the published nondegenerate induction functor.

## Actual quotient, fixed subtype and intrinsic helpers

All declarations are in
`Langlands.Algebra.NonUnitalModuleCornerInduction`. The module imports the
published construction by its Lean name and preserves its authorship.
It uses `rightCornerModule e` on the original additive group of `A`,
`cornerModule e Z` on the original additive group of `Z`, and the actual
`Tensor e Z`, with its inherited `tensorAddCommGroup` and original
residual action `tensorModule e Z`. In particular the tensor is the
published quotient of `A ⊗[ℤ] Z` by the balancing differences
`(a * c) ⊗ z - a ⊗ (c • z)`. Right multiplication by the corner unit is
`a * e`; no assertion makes it equal to `a`.

`InducedFixedPart e Z` transparently abbreviates
`NonUnitalModuleCorner.FixedPart e (ambientObject e Z)`. It therefore
uses exactly the published subgroup subtype, inherited additive group
and unital corner action, with the ambient object's named quotient and
residual original action.

`sandwichCorner e a` is the actual element of the corner with ambient
value `e * a * e`. Membership follows from the published
`Idempotent.mem_corner_iff_exists` with witness `a`, using idempotence
alone. `sandwichCorner_val` exposes its ambient value.
`fixedPartPureTensor e z` is the subtype-valued function with value
`tmul e e z`. Its membership proof rewrites the residual action on a
pure tensor as multiplication on the first factor and then uses
`e * e = e`. `fixedPartPureTensor_val` exposes its value.
These helpers construct no tensor inverse or linear equivalence.

## Pointwise predicates and closed targets

`CanonicalFixedPartEquivalence e Z E` is a predicate on an actual
corner-linear equivalence from `Z` to `InducedFixedPart e Z`. It records:

1. Equality of its entire forward function with `fixedPartPureTensor e`.
2. The forward evaluation `(E z).val = tmul e e z`.
3. The inverse evaluation
   `E.symm (projection e (tmul e a z)) = sandwichCorner e a • z`.
4. Both inverse identities as equalities of entire corner-linear maps.

The projection in item 3 explicitly uses `M := Tensor e Z` and
`hM := tensorModule e Z`. Its value is `tmul e (e * a) z`, by the actual
residual action. Projected pure tensors additively generate this fixed
subgroup: pure tensors additively generate the quotient and the
published projection is onto the fixed part. This explains the
inverse formula's scope; it is not an inverse certificate supplied to
the existence target.

`CornerInductionFixedPartEquivalenceTheorem` universally quantifies
the ring, idempotent, original additive group and ordinary corner-module
data and concludes existence of such an equivalence. It has no
equivalence, bijectivity, splitting or conclusion-bearing premise.

`restrictedInducedMap e f` is exactly the published restriction of the
whole original `inducedMap e f`, namely `id ⊗ f`. It explicitly supplies
`M := Tensor e Z`, `N := Tensor e Z'`, `hM := tensorModule e Z` and
`hN := tensorModule e Z'`. Its definition does not select a replacement
map by a pure-tensor formula.

`FixedPartEquivalenceNaturality e f E E'` records both whole-linear-map
equalities
`E'.toLinearMap.comp f = (restrictedInducedMap e f).comp E.toLinearMap`
and
`E'.symm.toLinearMap.comp (restrictedInducedMap e f) =
f.comp E.symm.toLinearMap`.
`CornerInductionFixedPartNaturalityTheorem` closes this assertion over
all ring/module data, maps and canonical witnesses. It is accompanied
by the unconditional existence target above; naturality alone is not
the principal existence assertion. The ring universe `uA` and both
module carrier universes `uZ`, `uZ'` are independent.

## Actual natural isomorphism and universe lift

`fixedPartInductionFunctor e` is the transparent composite
`ambientFunctor e ⋙ NonUnitalModuleCorner.functor e`. Its source is
`ModuleCat.{uZ} (Idempotent.Corner e)` and its target is
`ModuleCat.{max uA uZ} (Idempotent.Corner e)`. The actual tensor carrier
requires this target universe. The comparison functor is Mathlib's
existing `ModuleCat.uliftFunctor.{uA,uZ}`, whose objects have carriers
`ULift.{uA,uZ} Z` and whose maps are conjugated by `ULift.moduleEquiv`.

`CanonicalFixedPartNaturalIso e iso` requires, at every actual bundled
module `Z`, existence of a pointwise canonical equivalence `E` as
above, equality of the entire forward component map with
`E.toLinearMap.comp ULift.moduleEquiv.toLinearMap`, and equality of the
entire inverse component map with
`ULift.moduleEquiv.symm.toLinearMap.comp E.symm.toLinearMap`.
It also explicitly records
`((iso.hom.app Z).hom (ULift.up z)).val = tmul e e z`.
The `ULift.moduleEquiv` instances here have the displayed actual
source `ULift.{uA,uZ} Z` and target `Z`.
Since `iso` is an actual categorical natural isomorphism, its whole
component maps satisfy naturality and both inverse identities.

`CornerInductionFixedPartNaturalIsoTheorem` universally quantifies
`A` and `e` and concludes existence of this actual natural isomorphism
with its canonical component predicate. The isomorphism and its
pointwise correspondence are conclusions, with no supplied
categorical isomorphism or equivalence data.

`nondegenerateFixedPartInductionFunctor hA e` transparently denotes
`nondegenerateFunctor hA e ⋙
NonUnitalModuleCorner.nondegenerateFunctor e`.
`nondegenerateFixedPartInductionFunctor_eq` proves by reflexivity that
this entire functor equals `fixedPartInductionFunctor e`. Thus the
same actual quotient, inherited group, original action and whole maps
are retained, including the full restriction of `id ⊗ f`.
`NondegenerateCornerInductionFixedPartNaturalIsoTheorem` concludes
existence of the natural isomorphism to this precise composite and
uses the identical canonical component predicate by definitional
equality. It adds only the local-unit hypothesis needed to enter
the published nondegenerate category.

`CornerInductionFixedPartTheorem` is the conjunction, in order, of the
pointwise existence, independent-carrier naturality, ambient natural
isomorphism and nondegenerate-adapter closed targets. It is the single
exact target intended for the focused proof successor.

## Boundaries

The interfaces include zero idempotents and subsingleton rings or
modules. A zero corner permits only subsingleton ordinary unital
modules; the statements impose no impossible nonzero example.
The universe lift does not constrain either carrier universe to
contain the ring universe.

No principal target is proved in this module. The possible later
proof using the balanced pairing
`(a,z) ↦ sandwichCorner e a • z` is an alternate internal route, not
source evidence, an implemented proof or a premise here.
The two complex scalar structures mentioned by Renard, generatedness,
membership in `M(A,e)`, quotient comparisons, simple-class
correspondence, and equivalences of larger module categories remain
separate successors. This statement unit does not complete I.3.
