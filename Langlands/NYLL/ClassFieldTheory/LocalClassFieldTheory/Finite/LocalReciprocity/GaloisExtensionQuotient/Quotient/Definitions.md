# The abstract base-fixing extension quotient is the actual Galois group

Adapted by Worker 57 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/GaloisExtensionQuotient.lean`
(file SHA-256 `1f823480006ba2691c249c7e1f01f63300871f8c94ab6954be9105f913d4c831`).
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M089.009 | def `baseFixingExtensionQuotientEquivAmbient` (docstring 117–118, definition 119–130) | `baseFixingExtensionQuotientEquivAmbient` |
| M089.011 | def `baseFixingExtensionQuotientEquivGaloisGroup` (docstring 142–143, definition 144–157) | `baseFixingExtensionQuotientEquivGaloisGroup` |

Both original names are in the source namespace `LocalClassFieldTheory`; both
adapted names are in `Langlands.NYLL.LocalClassFieldTheory`.

These units lie in the dependency closure of Task 5264 but were not routed to
any task. Worker 5264, who routes that closure, agreed that Task 5799 stages
them in this directory. They are prerequisites of the source definition
`finiteGaloisAbstractExtensionOfEmbedding` (M097.005).

## Parameters

Both definitions take the source section variables of line 29,

```lean
variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
```

followed by the source binders `(E : IntermediateField K Ω) [IsGalois K E]`.
Both fields are in `Type` (universe zero), as in the source.

## Content

Write `G₀ = closedFixingSubgroup K Ω ⊥`, the closed subgroup of `Gal(Ω/K)`
fixing the bottom intermediate field (as a set, all of `Gal(Ω/K)`), and
`G_E = closedFixingSubgroup K Ω E`, the closed subgroup fixing `E`. The
inclusion proof `fixingSubgroupLeBase K Ω E : G_E ≤ G₀` is the published
M089.002 theorem. The class-formation quotient attached to `E/K` is the
quotient of the group `G₀.toSubgroup` by
`extensionSubgroup G₀ G_E (fixingSubgroupLeBase K Ω E)`, which is `G_E`
viewed as a subgroup of `G₀.toSubgroup`.

- `baseFixingExtensionQuotientEquivAmbient K Ω E` is a group isomorphism
  (`≃*`) from this class-formation quotient to the ordinary quotient
  `Gal(Ω / K) ⧸ G_E.toSubgroup`. It is the composite of
  `QuotientGroup.quotientMulEquivOfEq`, applied to the equality
  `extensionSubgroup G₀ G_E _ = (baseFixingToAmbientQuotient K Ω E).ker`, with
  `QuotientGroup.quotientKerEquivOfSurjective` (first isomorphism theorem) for
  the published map `baseFixingToAmbientQuotient K Ω E` (M089.006) and its
  published surjectivity theorem `baseFixingToAmbientQuotient_surjective`
  (M089.008). On a class `QuotientGroup.mk σ` it returns
  `QuotientGroup.mk σ.1`; this is the source theorem
  `baseFixingExtensionQuotientEquivAmbient_mk` (M089.010), which still holds by
  `rfl` for the adapted definition (checked privately). M089.010 is not part of
  this unit.
- `baseFixingExtensionQuotientEquivGaloisGroup K Ω E` is a group isomorphism
  from the same class-formation quotient to `Gal(E / K)`. It is the composite
  of `baseFixingExtensionQuotientEquivAmbient K Ω E`, Mathlib's
  `InfiniteGalois.normalAutEquivQuotient` for the closed normal subgroup `G_E`
  (normality from the published instance `closedFixingSubgroup_normal`,
  M089.004), and `AlgEquiv.autCongr` along
  `IntermediateField.equivOfEq (InfiniteGalois.fixedField_fixingSubgroup E)`.

Normality of `extensionSubgroup G₀ G_E _`, needed for the group structure on
the quotient, is found by instance search: the published `extensionSubgroup` is
an abbreviation for `G_E.toSubgroup.subgroupOf G₀.toSubgroup`, and instance
search returns Mathlib's `Subgroup.normal_subgroupOf` applied to the published
`closedFixingSubgroup_normal K Ω E` (checked privately by printing the
synthesized term). The source's own instance
`extensionSubgroupBase_normal` (M089.005) is not needed and is not included.

Published components used, all by their Library names:

- `Langlands.NYLL.RamificationTheory.closedFixingSubgroup`, through the
  modules below;
- `Langlands.NYLL.LocalClassFieldTheory.closedFixingSubgroup_normal` (M089.004)
  and `baseFixingToAmbientQuotient` (M089.006), from
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient.Initial.Definitions`;
- `Langlands.NYLL.LocalClassFieldTheory.fixingSubgroupLeBase` (M089.002),
  proved in `...GaloisExtensionQuotient.Initial.U002.Proofs`;
- `Langlands.NYLL.LocalClassFieldTheory.baseFixingToAmbientQuotient_surjective`
  (M089.008), proved in `...GaloisExtensionQuotient.Initial.U008.Proofs`;
- `Langlands.NYLL.CyclicCohomology.extensionSubgroup` (M004.002), from
  `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`.

## Modifications

- The source namespace `LocalClassFieldTheory` is prefixed by `Langlands.NYLL`.
  The two definitions are placed in their own file
  `GaloisExtensionQuotient/Quotient/Definitions`.
- The source imports the broad modules `AbsoluteUnitsFixedField` and
  `AbstractClassFieldTheory.Degree.Valuation`. The port imports the four
  published modules listed above and `Mathlib.FieldTheory.Galois.Infinite`.
  The source opens `RamificationTheory CyclicCohomology` and `ClassFormation`.
  The port opens `RamificationTheory CyclicCohomology`; `ClassFormation` is not
  used by these two definitions and is not opened.
- In `baseFixingExtensionQuotientEquivAmbient`, the source passes the theorem
  `baseFixingToAmbientQuotient_ker K Ω E` (M089.007) to
  `QuotientGroup.quotientMulEquivOfEq` (after `.symm`). M089.007 is stated in
  the Library (`baseFixingToAmbientQuotient_kerStatement`, module
  `...GaloisExtensionQuotient.Kernel.Statements`) but not proved. The port
  replaces that argument by a `show` term with the same equality
  `(baseFixingToAmbientQuotient K Ω E).ker = extensionSubgroup G₀ G_E _`, proved
  inline by the source proof of M089.007 (source lines 94–99) without its first
  step `rw [extensionSubgroup_base_eq_subgroupOf]`. That step rewrites with the
  source theorem M089.003, which is also unproved in the Library; it is not
  needed, because `extensionSubgroup` is an abbreviation and the following
  `change` closes the gap definitionally. The remaining steps
  (`ext x`, the `change` to
  `QuotientGroup.mk' G_E.toSubgroup x.1 = 1 ↔ x.1 ∈ G_E.toSubgroup`, and
  `QuotientGroup.eq_one_iff x.1`) are copied from the source. The same tactic
  block proves the published target `baseFixingToAmbientQuotient_kerStatement K Ω E`
  (checked privately). Only a proof argument changes, so by proof irrelevance
  the resulting equivalence is the source's.
- Everything else — the docstrings, the `def` keywords inside
  `noncomputable section`, the binders, the result types, the remaining terms
  of `baseFixingExtensionQuotientEquivAmbient` and the whole tactic body of
  `baseFixingExtensionQuotientEquivGaloisGroup` — is copied from source lines
  117–130 and 142–157 without change.
- No other declaration of the source module is included.

## Library and Mathlib comparison

A search of the Library `.lean` files (commit
`1bd55deac3796a0627d34ab2b1b6e8c36ac8b636`) found no declaration named
`baseFixingExtensionQuotientEquivAmbient` or
`baseFixingExtensionQuotientEquivGaloisGroup`, and no other equivalence out of
the quotient `G₀.toSubgroup ⧸ extensionSubgroup G₀ G_E _`. The terms
`closedFixingSubgroup K Ω ⊥` occur in the NYLL `GaloisExtensionQuotient` and
`SeparableFixedFieldNorm/Initial` modules only, and neither builds such an
equivalence. Mathlib's `InfiniteGalois.normalAutEquivQuotient` is used in
several non-NYLL modules (for example
`Langlands/ClassFieldTheory/Local/AbelianGaloisFiniteQuotients.lean`); there it relates a
quotient of a full Galois group `Gal(L/K)` to a Galois group, not the
class-formation quotient of `G₀.toSubgroup` by `extensionSubgroup`, so these
are not substitutes. M089.011 itself uses `normalAutEquivQuotient` as one
factor.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
