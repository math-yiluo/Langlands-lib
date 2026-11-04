# Nonpositive local ramification laws: proof

This module proves the unchanged closed proposition
`Langlands.NYLL.RamificationTheory.LocalField.LocalNonpositiveRamificationLawsStatement`
from the published [target](NonpositiveStatement.md). Its theorem, in
namespace `Langlands.NYLL.RamificationTheory.LocalField`, has the complete
type

```lean
theorem localNonpositiveRamificationLaws :
    LocalNonpositiveRamificationLawsStatement
```

The theorem has no outer term parameters, instances, hypotheses or universe
parameters. Both fields are in `Type` (universe 0), and the eight supplied
structures (`Field K`, `Field L`, `Algebra K L`, `FiniteDimensional K L`,
`IsGalois K L`, `ValuativeRel K`, `TopologicalSpace K` and
`IsNonarchimedeanLocalField K`) are those quantified inside the target.
The four conjuncts are, in order: upper and lower numbering agree at every
`t ≤ 0`; the lower group at every `t` with `-1 < t ≤ 0` equals the lower
group at index `0`; the upper group on the same interval equals the upper
group at index `0`; and the upper group at every `t ≤ -1` is the full
subgroup `⊤` of `Gal(L / K)`. "Index zero" means the group at the real
index `0`, not the trivial subgroup. The theorem depends only on the axioms
`propext`, `Classical.choice` and `Quot.sound`.

The module also exposes the four source laws as callable theorems in the
same namespace, under their source names and with the source's Type 0
telescope; they are projections of the proved target (see
[Source-named consequences](#source-named-consequences)).

## Imports and the actual groups

The module imports the published target, which imports the published
[local group definitions](Definitions.md), and three published proof
modules:
[the actual unique-extension Herbrand laws](../../HilbertRamification/HerbrandFunction/LawsProof.md),
[the generic Herbrand evaluations](../../Herbrand/Function/EvaluationProof.md)
and [the elementary real lower-group laws](../../HilbertRamification/RealLowerGroups/LowerGroupProof.md).
All published Lean/Markdown pairs, including the target pair, are unchanged.

`localLowerRamificationGroup K L t` and `localUpperRamificationGroup K L t`
are the published groups. Each installs, inside its body, the local
`_root_.Valuation.HasExtension (localCompleteDVF K).valuation
(chosenLocalExtensionCompleteDVF K L).valuation` witness
`Classical.choose (chosenLocalExtension_properties K L)`, and applies
`Higher.lowerRamificationGroup`, respectively
`Higher.upperRamificationGroupOfUniqueExtension`, to the base DVF
`(localCompleteDVF K).toDVF`, the target DVF
`(chosenLocalExtensionCompleteDVF K L).toDVF` and the uniqueness proof
`chosenLocalExtension_uniqueValuationExtension.{0} K L`. Write `huniq` for
this proof, `ψ` for
`Higher.inverseHerbrandFunctionOfUniqueExtension` and `φ` for
`Higher.herbrandFunctionOfUniqueExtension`, each on these two DVFs and
`huniq`, and `F` for
`Higher.lowerRamificationFiltrationOfUniqueExtension` on the same data. By
the published definition, the upper group at `t` is the lower group at
`ψ t`.

Every proof in this module that needs the extension instance introduces
exactly the same witness `Classical.choose (chosenLocalExtension_properties K L)`
by a proof-local `let` (the private helper also states it by a term-level
`letI` in its type, which is inlined). The module declares no instance,
global or local outside a proof, no alias and no new group, and it adds no
valuation or topology on `L`, extension, uniqueness, integral-closure,
finite-module or inverse-law premise.

## Private helper (M327.016)

`localInverseHerbrandFunction_eq_self_of_nonpos` is `private`. It takes the
target's Type 0 telescope as explicit fields and instance arguments, then
`(t : ℝ) (ht : t ≤ 0)`, and concludes `ψ t = t`. Its proof applies
injectivity of `φ`, from `Higher.herbrandFunctionOfUniqueExtension_strictMono`,
which reduces the goal to `φ (ψ t) = φ t`. That equation is the chain
`φ (ψ t) = t` (`Higher.herbrandFunctionOfUniqueExtension_psi`) and
`t = φ t`, the reverse of the generic
`DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction_of_nonpos`
applied to `F` and `ht`; `φ` unfolds definitionally to the generic Herbrand
function on `F`. The source uses `rw` with the inverse law; here the two
equations are joined by `Eq.trans`. The published groups apply the
uniqueness theorem, whose type is the Prop-valued
`ChosenLocalExtensionUniqueValuationExtensionStatement`; with the
uniqueness argument left for unification, `rw` failed to match the
pattern because that application is typed only after unfolding the
statement definition.

## Proof of the target

After introducing `K`, `L` and the eight structures and the local extension
witness, the proof establishes the first two clauses and then the last two.

1. Clause 1 (M327.017). For `t ≤ 0`, unfold both local groups and
   `Higher.upperRamificationGroupOfUniqueExtension`; the goal becomes
   `lowerRamificationGroup … (ψ t) = lowerRamificationGroup … t`, closed by
   rewriting with the private helper.
2. Clause 2 (M327.018). For `-1 < t ≤ 0`, `Int.ceil (t + 1) = 1` by
   `Int.ceil_eq_iff` and linear arithmetic, so the published
   `Higher.realRamificationExponent t`, which is `(Int.ceil (t + 1)).toNat`,
   equals `1`; the exponent at `0` is also `1`. Hence the two published
   ideals `Higher.realRamificationIdeal (chosenLocalExtensionCompleteDVF K L).toDVF t`
   and `… 0` (the maximal ideal to these exponents) are equal. After
   unfolding the lower group, subgroup extensionality and `change` expose
   membership as "every integral displacement lies in the ideal", and
   rewriting with the ideal equality closes it.
3. Clause 3 (M327.019). For `-1 < t ≤ 0`, rewrite with clause 1 at `t` and at
   `0` and with clause 2 at `t`.
4. Clause 4 (M327.020). For `t ≤ -1`, rewrite with clause 1 (as `t ≤ 0`),
   unfold the lower group, and apply the published
   `Higher.lowerRamificationGroup_eq_top_of_le_neg_one huniq ht`; the local
   witness supplies its extension instance.

## Source-named consequences

The four public theorems below lie in
`Langlands.NYLL.RamificationTheory.LocalField`. Each takes the explicit
`(K L : Type)` and the eight structures in the target's order, then the
source's real index and hypotheses, and is the corresponding projection of
`localNonpositiveRamificationLaws K L`. They are adapters of the proved
target, not new statement definitions.

| Source unit and lines | Public theorem | Arguments after the telescope | Conclusion | Proof |
| --- | --- | --- | --- | --- |
| M327.017, 877–890 | `localUpperRamificationGroup_eq_localLowerRamificationGroup_of_nonpos` | `(t : ℝ) (ht : t ≤ 0)` | `localUpperRamificationGroup K L t = localLowerRamificationGroup K L t` | `.1 t ht` |
| M327.018, 892–926 | `localLowerRamificationGroup_eq_zero_of_neg_one_lt_of_nonpos` | `(t : ℝ) (hneg : -1 < t) (ht : t ≤ 0)` | `localLowerRamificationGroup K L t = localLowerRamificationGroup K L 0` | `.2.1 t hneg ht` |
| M327.019, 928–943 | `localUpperRamificationGroup_eq_zero_of_neg_one_lt_of_nonpos` | `(t : ℝ) (hneg : -1 < t) (ht : t ≤ 0)` | `localUpperRamificationGroup K L t = localUpperRamificationGroup K L 0` | `.2.2.1 t hneg ht` |
| M327.020, 945–959 | `localUpperRamificationGroup_eq_top_of_le_neg_one` | `(t : ℝ) (ht : t ≤ -1)` | `localUpperRamificationGroup K L t = ⊤` | `.2.2.2 t ht` |

The telescope, argument names, endpoint hypotheses and conclusions are
those of the source theorems.

## Source and adaptations

The source is Naganori Yamaguchi's *ClassFieldTheory (NYLL)*,
[`Nyll/ValuedFieldTheory/Ramification/LocalField/Core.lean`, lines 846–959](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/LocalField/Core.lean#L846-L959),
commit `fbd320cd8b1b06487c58227e92eb135794267709`. The whole file has
SHA-256 `d0e79ce27df3b1f7481d2e6c89473f600acaf21f0cf4b678e29ba97a90792ecb`;
its header and setup (lines 1–54) and the complete passage 846–960 were
read. The readable snapshot is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No `notes/errata` directory was present in the workspace or supplied
Library. Compatibility patch P5 of the
[public port plan](../../../../../../notes/reuse/nyll-public-port-plan.md)
concerns original line 693, outside this passage. The source-order edges
in the [M327 partition](../../../../../../notes/reuse/nyll-public-port/m313-m336.md#m327)
were used only for scheduling; M327.006–.015 are not needed.

The mathematical route is the source's: M327.016 by injectivity, the
inverse law and the nonpositive Herbrand evaluation; M327.017 by unfolding
the upper group; M327.018 by the real exponent `1` on `(-1, 0]`; M327.019
from the first two; and M327.020 from the lower group's full range. The
changes are:

1. Namespaces gain `Langlands.NYLL`; the module opens only
   `Langlands.NYLL.LocalFieldTheory` and
   `Langlands.NYLL.RamificationTheory.HilbertRamification`, and writes the
   `Higher.` and generic Herbrand names accordingly. The source's seven
   wholesale imports become the published target and three proof modules.
2. The source's global M248.008 extension instance is replaced by the
   proof-local witness described above, the one installed by the published
   groups. The source's uniqueness alias M327.001
   `chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension` is not
   recreated; the published `chosenLocalExtension_uniqueValuationExtension.{0} K L`
   used by the groups is applied directly, at comparison universe 0.
3. M327.016 keeps its name and stays `private`; its type states the local
   witness by `letI`, and its final step uses `Eq.trans` instead of `rw`
   (see above).
4. The proofs of M327.017–M327.020 are placed inside the closed target as
   the four conjuncts, with the source steps (clause 4 uses
   `exact` after unfolding, as in the source). The four public theorems are
   then the target's projections, with unchanged names, telescopes and
   conclusions. Their docstrings are the source docstrings, prefixed by the
   source unit and, for M327.018 and M327.019, stating that the constant
   value is the index-zero group.
5. The `noncomputable section`, source `open` lines and `universe y` are
   omitted; no data are defined.

Worker 1237 implemented the adaptation, the closed-target proof, the four
adapters and this companion. Worker 106 supplied the source extraction,
target design and the proof dependency and route analysis.

The original copyright and authorship header is preserved verbatim:
Copyright (c) 2026 Naganori Yamaguchi
(`https://github.com/n-yamaguchi-0729`), all rights reserved;
authors: Naganori Yamaguchi (assisted by OpenAI Codex). The source is
Apache-2.0, and the Lean header records the modifications. The existing
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE), including their inherited
notices, remain unchanged, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`
respectively; `Core.lean` is not among NOTICE's listed third-party files.
The approved environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`, rather than upstream
Lean 4.35.0-rc2 and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.
