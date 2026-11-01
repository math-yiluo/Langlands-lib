# Canonical integer rings in finite separable local extensions

This module states the two conclusions of NYLL M248.003 and M248.004 as the
single closed proposition
`Langlands.NYLL.LocalFieldTheory.LocalCompleteDVFIntegerRingPropertiesStatement.{u,v}`.
The declaration has type `Prop`, with exactly the independent universe
parameters `u` and `v`. It supplies a target for a later proof.

## Complete proposition

The entire telescope below is inside the proposition:

```lean
∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [_root_.Valuation.HasExtension (ValuativeRel.valuation K)
    (ValuativeRel.valuation L)],
  IsIntegralClosure (ValuativeRel.valuation L).valuationSubring
    (ValuativeRel.valuation K).valuationSubring L ∧
  Module.Finite (ValuativeRel.valuation K).valuationSubring
    (ValuativeRel.valuation L).valuationSubring
```

The fields, field structures and algebra are supplied. The algebra is
finite-dimensional and separable. Each field independently has its supplied
valuative relation and topology satisfying Mathlib's
`IsNonarchimedeanLocalField`: the topology is valuative, locally compact, and
the valuative relation is nontrivial. There is no restriction to `Type 0`
and no equality or ordering requirement on `u` and `v`. The identity extension
is included.

For `vK := ValuativeRel.valuation K` and
`vL := ValuativeRel.valuation L`, the final hypothesis is exactly
`Valuation.HasExtension vK vL` for the supplied `Algebra K L`. Mathlib defines
this as `vK.IsEquiv (vL.comap (algebraMap K L))`; it allows equivalent
valuations without identifying their value groups or normalizations.
Integrality, module finiteness, henselianity, uniqueness and comparisons with
a chosen valuation are not premises.

## Actual rings, scalars and inclusions

Write `OK := vK.valuationSubring` and `OL := vL.valuationSubring`. These are
the actual subrings of `K` and `L`, whose elements satisfy `vK x ≤ 1` and
`vL y ≤ 1`. In the approved Mathlib,
`Mathlib/Topology/Algebra/Valued/ValuativeRel.lean` defines the source notation
`𝒪[K]` as `Valuation.integer (ValuativeRel.valuation K)`.
`Valuation.valuationSubring` extends `vK.integer` by its valuation-subring
property. Its underlying type and ring operations are definitionally those
of `vK.integer`. The same correspondence holds for `L`.

The supplied extension hypothesis makes the field algebra map restrict to
these rings: for `a : OK`,
`vL (algebraMap K L (a : K)) ≤ 1` follows from
`Valuation.HasExtension.val_map_le_one_iff` and `a.property`.
Mathlib's `Valuation.HasExtension.instAlgebra_valuationSubring` supplies the
resulting `Algebra OK OL`, using `instAlgebraInteger`. Thus

```lean
((algebraMap OK OL a : OL) : L) = algebraMap K L (a : K)
```

holds by reflexivity. The induced module action satisfies, for
`a : OK` and `b : OL`,
`((a • b : OL) : L) = algebraMap K L (a : K) * (b : L)`.
This is the action used by `Module.Finite OK OL`.

The algebra `OL → L` is the actual subring inclusion, and the algebra
`OK → L` is the inclusion into `K` followed by the supplied
`algebraMap K L`. Mathlib supplies
`Valuation.HasExtension.instIsScalarTower_valuationSubring` for `OK, K, L`
and `instIsScalarTower_valuationSubring'` for `OK, OL, L`.
Consequently the first conjunct is `IsIntegralClosure OL OK L` along those
maps: the inclusion `OL → L` is injective, and an element of `L` is integral
over `OK` exactly when it lies in the image of that inclusion. The second
conjunct asserts finite generation of `OL` as the displayed `OK`-module.
Neither conjunct chooses alternative rings or substitutes an abstract
equivalent ring.

The imported published `localCompleteDVF` packages exactly these canonical
valuations. Its definition is preserved, as are the published chosen
extension definitions. The separately published
`localCompleteDVFValuation_hasExtension` transfers the raw extension premise
to those canonical packages; the present proposition retains the raw premise
and writes the rings directly.

## Source correspondence and modifications

The original is Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF.lean),
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The full 206-line file was read; its SHA256 is
`f9f4741aa6a1584e125f571e6095b641f13f0983ccbda6225d9324b9fdc1f27c`.

| Source result | Source location | Adapted conclusion |
| --- | --- | --- |
| M248.003, `LocalFieldTheory.localCompleteDVF_integerRing_isIntegralClosure` | lines 77–96, signature 78–86 | first conjunct, `IsIntegralClosure OL OK L` |
| M248.004, `LocalFieldTheory.localCompleteDVF_integerRing_moduleFinite` | lines 98–110, signature 100–108 | second conjunct, `Module.Finite OK OL` |

Both signatures have the displayed shared telescope. Their proof bodies
are omitted. The adaptation groups the two conclusions under a single
universal quantifier, prefixes the namespace with `Langlands.NYLL`, and names
the resulting closed Prop. It expands `𝒪[K]` and `𝒪[L]` to their canonical
valuation subrings and spells `Valuation.HasExtension` with `_root_`.
The unused source universe `y` belongs to later uniqueness work.

The original imports are replaced by the published `Canonical` module and
focused Mathlib imports for separability, finite modules, integral closure
and valuation extensions. The module contains one Prop-valued definition,
without proofs or new global instances. The source proof's generic uniqueness
chain, the supplied/chosen comparison and reciprocity results remain separate
work. The approved environment is Lean 4.34.0 / Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`, environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`; upstream used Lean 4.35.0-rc2 /
Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

## Attribution

The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The supplement's publication manifest confirms the source file hash above.
The root NOTICE and the supplement's ValuedFieldTheory third-party source
table contain no entry for this selected file. No source-specific errata
directory exists in the workspace, project notes or current Library.

The original copyright and author header is retained verbatim. The inherited
Apache-2.0 [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) remain unchanged, with SHA256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
respectively. Existing imported adaptation credits remain in their files.

On 1 November 2026, Worker 106 supplied the closed target formulation and
original-to-adapted source comparison in this task's contract. Worker 384
checked that comparison against the pinned source and current Mathlib,
implemented the statement and wrote this explanation. Both are credited for
the reused formulation and adaptation.
