# Finiteness of the abstract quotient of a finite Galois intermediate extension

Adapted by Worker 57 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableUnitsNorm.lean`
(file SHA-256 `b725f9b453be02ebc61de24d8c9a3f32b87f438471b2423357c1edf54a76fcaa`).
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M096.003 | instance `baseFixingExtensionQuotient_finite` (docstring 64, declaration 65–73) | `baseFixingExtensionQuotient_finite` |

The original name is in the source namespace `LocalClassFieldTheory`; the
adapted name is
`Langlands.NYLL.LocalClassFieldTheory.baseFixingExtensionQuotient_finite`.

This module is a helper module of the candidate whose entry is
`finiteGaloisAbstractExtensionOfEmbedding` (M097.005,
`ConcreteReciprocityTransport/Extension/Definitions`). That definition uses
this instance as the proof of its `finite` field. The unit lies in the
dependency closure of Task 5264 but was not routed to any task. Worker 5264,
who routes that closure, agreed that Task 5799 stages it. Worker 5264 also
asked that it travel with a definition entry, because an instance of the
`Prop`-valued class `Finite` cannot be the entry declaration of a definition
candidate. The Library precedent is the instance `closedFixingSubgroup_normal`
(M089.004) inside `GaloisExtensionQuotient/Initial/Definitions`.

## Parameters

The instance takes the source section variables of lines 36–37 and 62,

```lean
variable (K : Type) (Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω]
variable (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E]
```

All fields are in `Type` (universe zero), as in the source. All three binders
`[IsGalois K Ω]`, `[FiniteDimensional K E]` and `[IsGalois K E]` are used, so
all are arguments of the instance.

## Content

Write `G₀ = closedFixingSubgroup K Ω ⊥` and `G_E = closedFixingSubgroup K Ω E`.
The instance states and proves that the class-formation quotient

```lean
Finite (G₀.toSubgroup ⧸ extensionSubgroup G₀ G_E (fixingSubgroupLeBase K Ω E))
```

is finite when `E/K` is a finite Galois intermediate extension of the Galois
extension `Ω/K`. Its proof transports finiteness of `Gal(E / K)` (a Mathlib
instance, since `E` is finite-dimensional over `K`) back along the equivalence
`baseFixingExtensionQuotientEquivGaloisGroup K Ω E` (M089.011) with
`Equiv.finite_iff`.

`Finite` is a `Prop`-valued class, so this instance is a proof. It contains no
data.

Published components used, all by their Library names:

- `Langlands.NYLL.LocalClassFieldTheory.baseFixingExtensionQuotientEquivGaloisGroup`
  (M089.011), from
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient.Quotient.Definitions`
  (candidate `154983ac-1004-41d1-ac31-be8597203b1d`, published in the Library
  at commit `3489c50380b46cfbdad8997457a217e6e8e6a27d`);
- through that module, `Langlands.NYLL.RamificationTheory.closedFixingSubgroup`,
  `Langlands.NYLL.LocalClassFieldTheory.fixingSubgroupLeBase` (M089.002) and
  `Langlands.NYLL.CyclicCohomology.extensionSubgroup` (M004.002).

## Modifications

- The source namespace `LocalClassFieldTheory` is prefixed by `Langlands.NYLL`.
  The instance is placed in its own file `SeparableUnitsNorm/Finite/Definitions`.
- The source imports `Mathlib.RingTheory.Norm.Transitivity` and three broad
  NYLL modules. The port imports only the published module that supplies
  M089.011. The source opens `RamificationTheory KummerTheory`,
  `LocalFieldTheory` and `ClassFormation CyclicCohomology`, and has
  `open scoped BigOperators`. The port opens `RamificationTheory CyclicCohomology`.
  The others are not used by this instance.
- The docstring, the `noncomputable instance` keywords, the binders, the
  statement and the proof term are copied from source lines 64–73 without
  change, inside the source section `FiniteGaloisIntermediate`.
- No other declaration of the source module is included.

## Library and Mathlib comparison

A search of the Library `.lean` files (commit
`3489c50380b46cfbdad8997457a217e6e8e6a27d`) found no declaration named
`baseFixingExtensionQuotient_finite`. It also found no other finiteness
statement for a quotient of `closedFixingSubgroup K Ω ⊥` by an extension
subgroup. The `Finite (K.toSubgroup ⧸ extensionSubgroup K _ _)` instances and
fields in the abstract class-formation modules (`FiniteGaloisSubextension`,
`FiniteAbelianSubextension`, `UnitCohomologyAxiom`, `FiniteAbstractField`) are
about abstract closed subgroups carrying their own finiteness data, not about
fixing subgroups of intermediate fields. Mathlib states finiteness of
`Gal(E / K)` for finite-dimensional `E`, which the proof uses. It has no
statement about the class-formation quotient.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
