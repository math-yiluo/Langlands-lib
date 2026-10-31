# Maximal-ideal completeness of finite integral closures

This module proves NYLL M245.014 as the single theorem
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosure_maximalIdeal_isAdicComplete_of_finite_separable.{u, v, w}`.
Its complete unapplied type is exactly the published closed proposition
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension.IntegralClosureMaximalIdealIsAdicCompleteOfFiniteSeparableStatement.{u, v, w}`.
Only the three independent universe levels parameterize the theorem.
The entry module is
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.MaximalIdealCompletenessProof`.
It imports the unchanged target from `MaximalIdealCompletenessStatements`.

## Mathematical content and actual objects

The target expands, in the published namespace, to

```lean
∀ (K : Type u) (L : Type w) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] (base : CompleteDVF.{u, v} K) [Algebra.IsSeparable K L],
  IsAdicComplete
    (CanonicalIntegralClosure.maximalIdeal (K := K) (L := L) base)
    (integralClosure base.valuation.valuationSubring L)
```

Thus `K` and `L` are fields with an arbitrary supplied `K`-algebra structure
on `L`, finite dimension and separability. The supplied bundle
`base : CompleteDVF.{u, v} K` stores a complete discrete valuation on `K`,
whose value group lies in `Type v`. The universes of the base field, value
group and extension field remain independent. Every finite separable
extension is included, including `L = K`.

Set `A := base.valuation.valuationSubring` and `B := integralClosure A L`.
The ring `A` is the actual valuation subring of the supplied valuation.
The ring `B` is Mathlib's actual integral-closure subalgebra of `L`. Its
`A`-algebra structure uses the inclusion `A → K`, followed by the supplied
`algebraMap K L`, corestricted to `B`. In particular, the scalar map
`algebraMap A B` is the same canonical map in every imported result.

The upstairs ideal is the published M245.007 definition
`CanonicalIntegralClosure.maximalIdeal (K := K) (L := L) base`.
It installs the proved witness
`integralClosure_isLocalRing_of_finite_separable.{u, v, w} K L base`
and returns `IsLocalRing.maximalIdeal B`, the ideal of non-units in `B`.
The proof installs precisely this witness locally when unfolding the ideal.

The conclusion uses the ordinary `B`-module structure on `B`.
`IsAdicComplete` is Mathlib's algebraic ideal-adic completeness class:
Hausdorffness and convergence of compatible sequences for the submodules
`I ^ k • ⊤`. No additional topology, local-ring structure, ideal equality,
completeness premise, chosen maximal ideal, extension valuation or alternative
integral-closure model is supplied as a hypothesis.

## Implemented proof

The proof follows the original argument.

1. Introduce exactly the data quantified inside the published proposition,
   name `A` and `B`, and install the published finite-separable localness
   theorem as a local `IsLocalRing B` witness. The `change` step unfolds the
   canonical maximal ideal to obtain the goal
   `IsAdicComplete (IsLocalRing.maximalIdeal B) B`. This is the same ideal
   with the same localness witness.
2. Apply the published M245.013 theorem
   `exists_integralClosure_base_maximal_map_eq_maximalIdeal_pow_pos`
   to `K`, `L` and `base` at universes `u, v, w`. It gives a natural number
   `n`, strict positivity `hnpos : 0 < n`, and an equality between the image
   of the base maximal ideal and the `n`th power of the canonical upstairs
   maximal ideal.
3. Apply the published M245.003 theorem
   `integralClosure_base_maximal_map_isAdicComplete_of_finite_separable`
   at the same universes and data. Its conclusion is
   `hmap : IsAdicComplete ((IsLocalRing.maximalIdeal A).map (algebraMap A B)) B`.
4. Unfold only `CanonicalIntegralClosure.maximalIdeal` in the equality from
   step 2, giving
   `hn' : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
     IsLocalRing.maximalIdeal B ^ n`.
   Rewriting `hmap` by `hn'` supplies the local instance
   `IsAdicComplete (IsLocalRing.maximalIdeal B ^ n) B`.
5. Apply the published M105.013 theorem
   `Langlands.NYLL.ValuationTheory.DiscreteValuationField.isAdicComplete_of_isAdicComplete_pow`
   to the ring `B`, its module `B`, its maximal ideal and `hnpos`.
   The generic theorem is specialized at universes `w, w`, since both its
   ring and module are `B : Type w`. This yields the desired completeness.

The positive exponent, image-ideal completeness and localness are proved
dependencies, not additional premises. All instance setup stays inside this
proof. No helper declaration, global instance or axiom is added.

## Source correspondence and modifications

The original is Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteIntegralClosure.lean`.
Worker 384 read lines 1–64 and 428–457, including the independent universe
declaration at line 23, ambient field/algebra/finite-dimensional variables
at lines 30–31, and the complete M245.014 proof.

| Original declaration or use | Adapted declaration or use |
| --- | --- |
| M245.014 `ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosure_maximalIdeal_isAdicComplete_of_finite_separable`, lines 430–457 | Same theorem name with the `Langlands.NYLL` prefix, proving the unchanged closed target |
| M245.006 `integralClosure_isLocalRing_of_finite_separable` | Published theorem imported through `IdealPowerPosProof`, installed locally |
| M245.007 `CanonicalIntegralClosure.maximalIdeal` | Unchanged published definition used by the target and power equality |
| M245.013 `exists_integralClosure_base_maximal_map_eq_maximalIdeal_pow_pos` | Published theorem imported from `FiniteIntegralClosure.IdealPowerPosProof` |
| M245.003 `integralClosure_base_maximal_map_isAdicComplete_of_finite_separable` | Published theorem imported from `FiniteIntegralClosure.CompletenessProofs` |
| M105.013 `ValuationTheory.DiscreteValuationField.isAdicComplete_of_isAdicComplete_pow` | Published theorem imported from `DiscreteValuationField.AdicPowerCompletenessProof` |

Worker 384 adapted this proof and wrote its English companion on
31 October 2026. The adaptation prefixes the namespace with `Langlands.NYLL`
and gives the theorem its exact closed-target type with explicit independent
universe levels. It expands the source abbreviations `base.valuationSubring`
and `base.maximalIdeal` to `base.valuation.valuationSubring` and its
`IsLocalRing.maximalIdeal`, adding the local name `A`. Applications of the
published closed theorems supply their universes and arguments explicitly.
The two source `simpa` steps use `simpa only` with the canonical-ideal
definition and the ideal equality, respectively. The source's broad imports
are replaced by the four focused published target/proof modules. The
localness witness, scalar maps and positive-power proof route are preserved.

Worker 106 supplied routing and source observations without an implementation
draft. Published results are imported by Lean name; no other worker's
unpublished implementation draft was reused. The target and all its imports
remain unchanged. This unit proves maximal-ideal completeness; extension
valuations, host comparisons, inertia and reciprocity are separate units.

## Source records and attribution

Registered source `external-lean-reuse-snapshots-2026-10-21` has fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The readable pinned source root is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The verified SHA256 of `FiniteIntegralClosure.lean` is
`43c21425b2c39e7e6e5d2bca1f2b615c5c29e9d91e69d32d079e593df3170094`.
Registered supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Its ValuedFieldTheory source table and the upstream NOTICE contain no
source-specific entry for `FiniteIntegralClosure.lean`. No applicable project
erratum was found in the workspace, project notes or current Library notes.

The original copyright and author header is preserved verbatim: copyright
2026 Naganori Yamaguchi; authors Naganori Yamaguchi (assisted by OpenAI
Codex); released under Apache-2.0. The unchanged
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) accompany the adaptation.
The Lean header records the modifications.

The approved environment is Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`; upstream used
Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.
