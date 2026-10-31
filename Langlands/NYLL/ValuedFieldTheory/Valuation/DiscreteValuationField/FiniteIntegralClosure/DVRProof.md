# The finite integral closure over a complete DVF is a DVR

The module proves NYLL M245.011 as the exact published closed proposition
`IntegralClosureIsDiscreteValuationRingOfFiniteSeparableStatement.{u, v, w}`.
The public theorem is
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosure_isDiscreteValuationRing_of_finite_separable`.
Its complete unapplied type is that target constant, with independent universe
parameters `u, v, w` in that order and no additional declaration arguments.

The entry module is
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.DVRProof`.
The published target in `FiniteIntegralClosure.DVRStatements` and all
published dependencies are used unchanged.

## Original-to-adapted declaration map

| Source (`ValuationTheory.DiscreteValuationField.ValuedExtension`) | Adapted declaration |
| --- | --- |
| theorem `integralClosure_isDiscreteValuationRing_of_finite_separable` (lines 329–353) | theorem `Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosure_isDiscreteValuationRing_of_finite_separable.{u, v, w}`, of type `IntegralClosureIsDiscreteValuationRingOfFiniteSeparableStatement.{u, v, w}` |
| uses `integralClosure_isLocalRing_of_finite_separable` (M245.006) | the published theorem of the same name (with the `Langlands.NYLL` prefix) in `FiniteIntegralClosure.LocalnessProof` |
| uses `integralClosure_not_isField_of_finite_separable` (M245.010) | the published theorem of the same name (with the `Langlands.NYLL` prefix) in `FiniteIntegralClosure.NotFieldProof` |
| uses `base_valuationSubring_isFractionRing` (`IntegralClosure.lean`, lines 471–474) | not ported; Mathlib's instance `ValuationSubring.instIsFractionRingSubtypeMem` is found by instance search |

No other declaration is added.

## Data, universes and scalar maps

The target quantifies, in order, over
`(K : Type u) (L : Type w) [Field K] [Field L] [Algebra K L]
[FiniteDimensional K L] (base : CompleteDVF.{u, v} K) [Algebra.IsSeparable K L]`
and concludes
`IsDiscreteValuationRing (integralClosure base.valuation.valuationSubring L)`.
The proof introduces exactly these parameters. The `K`-algebra structure on
`L` and the complete discrete valuation `base` are arbitrary supplied data. The
theorem covers every finite separable extension, including the trivial
extension `L = K`. The value group stored in `base` lies in `Type v`. None of
the three universes is identified with another.

Write `A := base.valuation.valuationSubring`, the actual valuation subring of
`K`, and `B := integralClosure A L`, the actual Mathlib subalgebra of elements
of `L` integral over `A`. The rings `A` and `B` lie in `Type u` and `Type w`,
respectively. `A` carries `ValuationSubring.instCommRingSubtypeMem`. The
algebra structure of `L` over `A` is Mathlib's `Algebra.ofSubsemiring`: the
inclusion `A → K` followed by `algebraMap K L`. `B` carries its subalgebra ring
structure `Subalgebra.toCommRing`, and its scalar maps from `A` and to `L` are
the subalgebra structures (`Subalgebra.algebra` and `Subalgebra.toAlgebra`).
The integral domain instance on `B` is Mathlib's
`instIsDomainSubtypeMemSubalgebraIntegralClosure`
(`Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean`, line 659),
which uses that the field `L` is a domain.

## Implemented proof

1. Localness. The published theorem
   `integralClosure_isLocalRing_of_finite_separable.{u, v, w} K L base`
   (M245.006) gives `IsLocalRing B`, held as a local instance (`have`).
2. Dedekind property. Mathlib's `integralClosure.isDedekindDomain A K L`
   (`Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean`, line 234, which
   applies `IsIntegralClosure.isDedekindDomain`, line 220) gives
   `IsDedekindDomain B`. Its hypotheses are supplied by instance search:
   - `IsFractionRing A K`: Mathlib's `ValuationSubring.instIsFractionRingSubtypeMem`
     (`Mathlib/RingTheory/Valuation/ValuationSubring.lean`, line 153);
   - `IsScalarTower A K L`: Mathlib's `Submonoid.instIsScalarTowerSubtypeMem`
     (`Mathlib/Algebra/Group/Submonoid/MulAction.lean`, line 58) applied to
     `IsScalarTower.left` for `K`, `K`, `L`;
   - `IsDedekindDomain A`: Mathlib's `IsPrincipalIdealRing.isDedekindDomain`
     (`Mathlib/RingTheory/DedekindDomain/Basic.lean`, line 170) from the
     principal ideal ring part of `IsDiscreteValuationRing A`, which is
     Mathlib's `Valuation.valuationSubring_isDiscreteValuationRing`
     (`Mathlib/RingTheory/Valuation/Discrete/Basic.lean`, line 449). That
     instance uses the cyclic and nontrivial value group coming from the
     `IsRankOneDiscrete` instance of `base.valuation`, which is the published
     projection `Valuation.IsCompleteDiscrete.isRankOneDiscrete` of the stored
     field `base.instCompleteDiscrete` (`Complete.Definitions`);
   - `IsDomain A`: `ValuationSubring.instIsDomainSubtypeMem`; `IsDomain B` as
     above; and the given `[FiniteDimensional K L]` and
     `[Algebra.IsSeparable K L]`.
3. Not a field. The published theorem
   `integralClosure_not_isField_of_finite_separable.{u, v, w} K L base`
   (M245.010) gives `¬ IsField B`. Its target does not assume finite
   dimensionality, so it applies here directly.
4. Conclusion. Mathlib's `IsDiscreteValuationRing.TFAE B hB`
   (`Mathlib/RingTheory/DiscreteValuationRing/TFAE.lean`, line 210) is the
   list of equivalent conditions for a Noetherian local domain that is not a
   field. Its `IsNoetherianRing B` argument is obtained by instance search from
   the Dedekind proof of step 2 (through `IsDedekindDomain.toIsDedekindRing`
   and `IsDedekindRing.toIsNoetherian`), its `IsLocalRing B` argument is step
   1, and its `IsDomain B` argument is the instance above. `List.TFAE.out`
   with the one-based indices `3` (`IsDedekindDomain B`) and `1`
   (`IsDiscreteValuationRing B`) turns the Dedekind proof into
   `IsDiscreteValuationRing B`.

A private check in the approved environment printed the theorem with explicit
instances and confirmed the instance resolutions above with `#synth`, the use
of the TFAE indices, and that the trivial extension `L = K` is an instance of
the theorem. Inspection of the theorem reports kind `theorem`, universe
parameters `u, v, w`, and only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Source correspondence and adaptations

The source is Naganori Yamaguchi's ClassFieldTheory at commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteIntegralClosure.lean`:
universe line 23, ambient variables 30–31 (including
`[FiniteDimensional K L]`), docstring 329–330, signature 331–334 and proof
335–353. The fraction-ring wrapper is in
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/IntegralClosure.lean`,
lines 471–474; it is the generic Mathlib fact
`(Valuation.valuationSubring.integers (v := base.valuation)).isFractionRing`.

The proof keeps the source route: localness (M245.006), the base fraction-ring
property, Mathlib's `integralClosure.isDedekindDomain`, nonfield (M245.010)
and the Dedekind-to-DVR direction `(IsDiscreteValuationRing.TFAE _ _).out 3 1`.
The explicit modifications are:

- The closed-target signature, the explicit independent universes `u, v, w`,
  and the source abbreviation `base.valuationSubring` expanded to the actual
  valuation subring `base.valuation.valuationSubring`.
- The source installs `IsFractionRing A K` as a local instance through the
  wrapper `base_valuationSubring_isFractionRing`; here instance search finds
  Mathlib's `ValuationSubring.instIsFractionRingSubtypeMem` directly, so the
  wrapper is not ported.
- The source installs `IsDomain B` with `infer_instance` as a local instance;
  here instance search finds it directly.
- The source proves `IsNoetherianRing B` separately with
  `integralClosure.isNoetherianRing`; here it is the Noetherian part of the
  Dedekind proof, so that step is omitted.
- The source passes the Dedekind property through a local instance and
  `show ... from inferInstance`; here the Dedekind proof is named and passed
  directly.
- The NYLL upstream imports are replaced by the published target, the
  published M245.006 and M245.010 proof modules and focused Mathlib imports.

Worker 106 supplied routing and source/API observations only, no
implementation draft, and no other worker's adapted Lean content was reused.
The published localness proof (by Worker 1045) and nonfield proof (by Worker
764) are imported as Library declarations; their Lean content is not copied.

## Imports and scope

The direct imports are the published `FiniteIntegralClosure.DVRStatements`
(the target, which imports the published `Complete.Definitions`),
`FiniteIntegralClosure.LocalnessProof` (M245.006) and
`FiniteIntegralClosure.NotFieldProof` (M245.010), plus Mathlib's
`RingTheory.DedekindDomain.IntegralClosure`
(`integralClosure.isDedekindDomain`), `RingTheory.DiscreteValuationRing.TFAE`
(`IsDiscreteValuationRing.TFAE`) and `RingTheory.Valuation.Discrete.Basic`
(the discrete valuation ring instance of the valuation subring).

The only public addition is M245.011's proof. There is no added hypothesis,
helper declaration, global instance, axiom, chosen extension valuation,
module-finiteness, faithfulness, localness, Noetherian, Dedekind, nonfield or
discrete valuation ring assumption on `B`; localness and the nonfield property
are the published proofs about the actual `B`. The adic completeness of `base`
enters only through the published localness theorem. Ideal powers, extension
valuations, local-field comparisons, inertia and reciprocity are not treated
here.

## Attribution and source records

The registered source `external-lean-reuse-snapshots-2026-10-21` has fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The source root is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The verified SHA256 of `FiniteIntegralClosure.lean` is
`43c21425b2c39e7e6e5d2bca1f2b615c5c29e9d91e69d32d079e593df3170094`, and that
of `IntegralClosure.lean` is
`b0309db3073ffb278f6558c442acc19ab72ba76ed32ce4d88a63b953e65c86c2`.

The attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
It has no entry specific to `FiniteIntegralClosure.lean`. No applicable
erratum was found.

The original copyright and author header is retained verbatim: copyright 2026
Naganori Yamaguchi; authors Naganori Yamaguchi (assisted by OpenAI Codex), under
Apache-2.0. The existing unmodified
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) accompany this adaptation.
Worker 764 made the modifications listed above on 30 October 2026 and wrote
this Markdown. The approved environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
