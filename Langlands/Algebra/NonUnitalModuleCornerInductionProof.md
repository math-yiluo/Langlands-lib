# The actual fixed-part induction isomorphism and naturality

Worker 1187 proves the unchanged closed proposition
`Langlands.Algebra.NonUnitalModuleCornerInduction.CornerInductionFixedPartTheorem`
from `Langlands.Algebra.NonUnitalModuleCornerInductionStatements`.
The proof declaration is
`Langlands.Algebra.NonUnitalModuleCornerInduction.cornerInductionFixedPart`.
Its universe parameters are the independent `uA`, `uZ` and `uZ'`.

## Source and scope

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
at `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
The relevant passages are the conventions at printed pages 5–7 / PDF pages
11–13, I.2.1–I.2.2 at printed pages 14–16 / PDF pages 20–22, and
I.3.1–I.3.2 at printed pages 19–20 / PDF pages 25–26. Formula (I.3.2.1),
printed page 20 / PDF page 26, identifies a unital corner module with the
fixed part of its actual induction by `z ↦ e ⊗ z`, naturally in `Z`.

The registered supplementary `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
is at `/home/taskhub/pilot/literature/Renard — Représentations des groupes réductifs p-adiques- corrections et compléments (2010 edition errata).pdf`.
Its PDF pages 1–2 warn that the right corner action on `A` need not be
unital and give a corrected injectivity argument. The governing 2026 passage
already includes these corrections. The cited passages were read from the
saved native extraction of these exact source files.

Renard works with a complex algebra with local idempotent units. The published
statement proved here is an internal additive strengthening: the pointwise
and ambient categorical results require only an associative `NonUnitalRing A`,
an actual idempotent `e`, and an ordinary unital module over the actual corner
`Idempotent.Corner e`. There are no assumptions of commutativity, nontriviality,
faithfulness, dimension, a complex action or local units in those conclusions.
Only the adapter to the published nondegenerate category uses
`IsIdempotented A`. The proof does not supply the separate complex scalar
comparison. The implemented inverse route is an internal direct sandwich
construction; it does not formalize the source's `Hom`-valued pairing.

## Descent through the original quotient

Throughout the file the named original actions `rightCornerModule`,
`cornerModule` and `tensorModule` are selected locally. The tensor remains
exactly `Tensor e Z`, the published additive balanced quotient of the integer
tensor product, with the inherited additive group. The fixed carrier remains
`InducedFixedPart e Z`, the published subgroup subtype of `ambientObject e Z`,
with its published unital corner module structure. No imported file is changed.

The elementary private sandwich identities prove preservation of zero and
addition, `sandwichCorner e e = 1`, invariance under left multiplication by
`e`, and

```
sandwichCorner e (a * c.val) = sandwichCorner e a * c.
```

Here `c` is in the actual corner; its ambient value satisfies both
`e * c.val = c.val` and `c.val * e = c.val`. Associativity and these absorption
identities suffice, including in the noncommutative case.

`sandwichPairing e Z` is the actual biadditive map
`A →+ Z →+ Z` with value `sandwichCorner e a • z`. The last identity and
`mul_smul` prove `sandwichPairing_balanced` for the original right and left
actions. `sandwichLift e Z` then invokes the published
`NonUnitalModuleTensor.lift`, descending this pairing through the actual
balancing relations. Its pure-tensor formula is `sandwichLift_tmul`.

`fixedPartLinearMap e Z` has forward function exactly the published
`fixedPartPureTensor e`; its ambient value is `tmul e e z`. Additivity comes
from the quotient's pure-tensor additivity. For corner-linearity, balancing
moves `c` between the two factors and its two absorption identities identify
the result with the original residual action of `c.val` on the fixed tensor.

The first inverse identity, `sandwichLift_fixedPartLinearMap`, follows from
`sandwichCorner e e = 1` and the ordinary module's unit law. The second is
proved as the equality of entire additive maps
`fixedPartLinearMap_comp_sandwichLift`: the composite on all tensors is
exactly the published `NonUnitalModuleCorner.projection`. The proof uses
`NonUnitalModuleTensor.hom_ext`; on a pure tensor its ambient equality is

```
e ⊗ ((eae) • z) = (eae) ⊗ z = (ea) ⊗ z.
```

The first step balances with the sandwich element, and the second balances
with the corner unit and uses `1 • z = z`. It never asserts `a * e = a` in
`A`. Projection is the identity on its fixed subtype, so restricting
`sandwichLift` to that subtype gives the right inverse.

`fixedPartEquivalence e Z` packages the forward linear map and this explicit
inverse into a corner-linear equivalence. `fixedPartEquivalence_canonical`
checks every conjunct of the published canonicality predicate: the entire
forward function, its ambient tensor values, the inverse evaluation on
`projection e (tmul e a z)`, and both identities as whole corner-linear
maps. The inverse evaluation additionally uses
`sandwichCorner e (e * a) = sandwichCorner e a`.
`cornerInductionFixedPartEquivalence` closes existence over all ring and
module data.

## Whole-map naturality and the actual lifted comparison

`cornerInductionFixedPartNaturality` proves the published closed naturality
target for arbitrary canonical witnesses `E` and `E'`, with independent
carrier universes `uZ` and `uZ'`. The forward whole-map equality follows by
linear-map and subtype extensionality from the canonical ambient evaluations
and the published `inducedMap_tmul`. The map being restricted remains the
whole original `inducedMap e f = id ⊗ f`, under both named tensor actions.
Applying the target equivalence to both sides and using the forward equality
at `E.symm x` proves the inverse whole-map equality.

`fixedPartNaturalIso e` is an actual `NatIso.ofComponents` from Mathlib's
`ModuleCat.uliftFunctor.{uA,uZ} (Idempotent.Corner e)` to the published
`fixedPartInductionFunctor e`. At an actual bundled module `Z` its component
is the module-category isomorphism associated to

```
ULift.{uA,uZ} Z ≃ₗ[Idempotent.Corner e] Z ≃ₗ[Idempotent.Corner e] InducedFixedPart e Z,
```

using the actual `ULift.moduleEquiv` followed by `fixedPartEquivalence`.
Component naturality reduces to `inducedMap_tmul`. The source carriers are
`ULift.{uA,uZ} Z` and the target carriers lie in `Type (max uA uZ)`;
no restriction on the relative sizes of `uA` and `uZ` is imposed.
`fixedPartNaturalIso_canonical` identifies both entire component maps with
the specified compositions of the pointwise equivalence, its inverse and
`ULift.moduleEquiv` in the required directions. It also records the ambient
value `tmul e e z` on every `ULift.up z`.

`cornerInductionFixedPartNaturalIso` closes the ambient existence assertion.
`nondegenerateCornerInductionFixedPartNaturalIso` reuses the same actual
natural isomorphism: the published composite through the nondegenerate
category is definitionally equal to the ambient fixed-part composite. Its
local-unit assumption serves only to enter that category. Finally,
`cornerInductionFixedPart` bundles these three conclusions and the whole-map
naturality theorem in the precise order of the unchanged published target.

## Boundaries

Zero idempotents and subsingleton rings or modules are included by the
unrestricted proof; no nonzero element is selected. The two complex scalar
structures, generatedness and membership in `M(A,e)`, quotient comparisons,
simple-class correspondence, and larger module-category equivalences remain
separately owned successors. This proof does not complete I.3 or the whole
book. Compilation is development evidence; independent proof acceptance and
Library publication are separate requirements.
