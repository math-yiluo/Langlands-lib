# NYLL M327.006: local upper-ramification transport along an algebra equivalence

This module proves the exact published target
`Langlands.NYLL.RamificationTheory.LocalField.localUpperRamificationGroup_map_autCongrStatement`
under the adapted source name `localUpperRamificationGroup_map_autCongr` in that
namespace. The target retains `K L M : Type`, all field/algebra/finite-dimensional
Galois hypotheses and the base's nonarchimedean local-field hypotheses, and uses
the published chosen-extension `localUpperRamificationGroup` for every real t.
The complete theorem type is the closed proposition
`localUpperRamificationGroup_map_autCongrStatement`; after unfolding it, its
body is:

```lean
∀ (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M]
  [FiniteDimensional K L] [FiniteDimensional K M]
  [IsGalois K L] [IsGalois K M]
  [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (e : L ≃ₐ[K] M) (t : ℝ),
  Subgroup.map (AlgEquiv.autCongr e).toMonoidHom
      (localUpperRamificationGroup K L t) =
    localUpperRamificationGroup K M t
```

There are no universe parameters and no supplied valuation or topology on
either extension field. All groups are subgroups of the actual algebra
automorphism groups `Gal(L/K)` and `Gal(M/K)`.

## Published inputs

The proof imports the following existing Library modules without changing them:

- `Langlands.NYLL.ValuedFieldTheory.Ramification.LocalField.Core.AutCongrStatement`,
  for the exact target and the actual local groups.
- `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ValuationTransport.Definitions`,
  for `Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.valuationSubringRingEquivOfComap`.
- `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction.LawsProof`,
  for `Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.herbrandFunctionOfUniqueExtension_strictMono`
  and `.herbrandFunctionOfUniqueExtension_psi`.
- `Langlands.NYLL.ValuedFieldTheory.Ramification.Herbrand.Function.EvaluationProof`,
  for `Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction_eq_of_card_lower_eq`.

The target's imports already provide
`Langlands.NYLL.LocalFieldTheory.localCompleteDVF`,
`.chosenLocalExtensionCompleteDVF`, `.chosenLocalExtension_properties` and
`.chosenLocalExtension_uniqueValuationExtension`, together with the actual
lower groups, filtrations, Herbrand functions and upper groups. The only
additional Mathlib import is `Mathlib.RingTheory.LocalRing.RingHom.Basic`.

## Implemented route

The proof pulls back only the chosen valuation on M along the base-linear
algebra equivalence e. Base-linearity and `Valuation.HasExtension.val_map_le_one_iff`
show locally that this valuation extends the chosen base valuation. Applying
`chosenLocalExtension_uniqueValuationExtension.{0} K L` directly to that
valuation and `Valuation.isEquiv_iff_valuationSubring` identifies its valuation
ring with the chosen ring on L. `RingEquiv.subringCongr` and the published
`valuationSubringRingEquivOfComap` give the induced ring equivalence r from the
chosen ring on L to the chosen ring on M. All extension witnesses come from
`Classical.choose (chosenLocalExtension_properties K L)` or its M counterpart,
or are locally constructed; no global instance is added.

Mathlib `IsLocalRing.map_ringEquiv_maximalIdeal` and `Ideal.map_pow` transport
the real ramification ideals. The underlying ring map of r is e, so it
intertwines the valuation-ring actions under `AlgEquiv.autCongr e`. Membership
in lower groups is therefore equivalent. This gives equality of mapped lower
groups and of their finite cardinalities. The published
`Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction_eq_of_card_lower_eq`
identifies their Herbrand functions. Published strict monotonicity and the
inverse identities identify inverse Herbrand functions. Evaluating the lower
transport at the common inverse parameter proves the upper transport.

This route avoids the source's pulled complete DVF and final M307.006
valuation-ring-independence comparison: chosen uniqueness applies to an
arbitrary valuation, so the chosen rings can be compared directly. It also
avoids the generic finite-separable uniqueness and complete-comap helpers.
The explicit uniqueness types keep the comparison value-group parameter
universally quantified during elaboration. No global `Valuation.HasExtension`
instance is introduced. Proof irrelevance identifies the locally obtained
extension witnesses with the witnesses in the published local-group
definitions, so the final `change` reduces the exact target to the proved
upper-group equality.

## Source and changes

Naganori Yamaguchi, *ClassFieldTheory*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/Ramification/LocalField/Core.lean`, M327.006,
signature lines 117–128 and proof lines 131–341. The proof adapts the source's
ideal, displacement, lower-group, cardinality, and Herbrand comparisons.
The whole-file SHA-256 is
`d0e79ce27df3b1f7481d2e6c89473f600acaf21f0cf4b678e29ba97a90792ecb`.
Worker 296 replaced the pulled complete-DVF construction by direct chosen-ring
transport as above, reused Mathlib maximal-ideal transport, prefixed namespaces,
closed the theorem over its published target, and narrowed imports. No target
hypothesis, universe, actual group or conclusion is changed.

Registered source `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The original copyright and author header and existing `licenses/NYLL/LICENSE`
and `licenses/NYLL/NOTICE` are retained unchanged, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
respectively. No matching NYLL-specific erratum was found in the available
errata filenames.

Worker 288 reused Worker 296's complete implementation from Task 5884's
shared draft revision 5, checked it against the pinned original and published
inputs, and prepared this focused proof pair and documentation for Task 6217.
Worker 296 is credited as a coauthor. The environment is
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Compilation is development
evidence; exact-target validation, independent semantic review and integration
establish acceptance and publication.

The focused module passed development check
`a7e686da-0cb8-4472-bddf-0a363cc52d21` with no errors or warnings.
Inspection reported the indicated theorem, no universe parameters, and only
`propext`, `Classical.choice` and `Quot.sound` as axioms. This check does not
itself supply independent acceptance.
