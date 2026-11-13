# NYLL M071.003: injectivity of the intermediate quotient inclusion

This module proves the published Library proposition
`Langlands.NYLL.ClassFormation.transferNormNaturalityIntermediateInclusion_injectiveStatement`
by the theorem
`Langlands.NYLL.ClassFormation.transferNormNaturalityIntermediateInclusion_injective`.
The theorem's type is exactly that proposition applied to its source
parameters,
`transferNormNaturalityIntermediateInclusion_injectiveStatement K K' L hLK' hK'K`,
with the implicit group, its two structures and the two normality instances
supplied by elaboration.

Its sole direct import is
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainTransfer.Intermediate.Statements`.
That published Lean/Markdown pair and its complete imported chain remain
unchanged.

## Target and parameters

As in the statement module, the section variables are
`{G : Type u} [Group G] [TopologicalSpace G]` for an arbitrary universe `u`.
The theorem then has, in this order, explicit closed subgroups
`K K' L : ClosedSubgroup G`, explicit `hLK' : L.toSubgroup ≤ K'.toSubgroup`
and `hK'K : K'.toSubgroup ≤ K.toSubgroup`, and the named instances
`hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal` and
`hL'normal : (L.toSubgroup.subgroupOf K'.toSubgroup).Normal`.

Unfolding the published proposition gives

```lean
Function.Injective
  (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K)
```

Here `transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K` is the
published monoid homomorphism (M071.001, `MainTransfer/Intermediate/Definitions`)
`K'.toSubgroup ⧸ L.toSubgroup.subgroupOf K'.toSubgroup →*
K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup`, defined as the
published `finiteReciprocityNaturalityRestriction K K' L L (hLK'.trans hK'K)
hLK' hK'K le_rfl` (`MainNaturality/Restriction/Definitions`), which is
Mathlib's `QuotientGroup.map` of `Subgroup.inclusion hK'K`. It sends the
class of `k' : K'` modulo `L` to the class of the same element, viewed in
`K`, modulo `L` (the content of M071.002). The statement says that
`G(L/K')` embeds in `G(L/K)`.

## Implemented proof

The complete proof body is

```lean
  intro x y
  refine QuotientGroup.induction_on x ?_
  intro k'
  refine QuotientGroup.induction_on y ?_
  intro l' h
  apply QuotientGroup.eq.mpr
  apply Subgroup.mem_subgroupOf.2
  have hmem :
      (Subgroup.inclusion hK'K k')⁻¹ *
          Subgroup.inclusion hK'K l' ∈
        L.toSubgroup.subgroupOf K.toSubgroup :=
    QuotientGroup.eq.mp h
  have hG := Subgroup.mem_subgroupOf.1 hmem
  simpa using hG
```

1. `intro x y` unfolds the published proposition and `Function.Injective`.
   Two applications of `QuotientGroup.induction_on` reduce to classes of
   representatives `k' l' : K'.toSubgroup`, with
   `h : transferNormNaturalityIntermediateInclusion … (QuotientGroup.mk k') =
   transferNormNaturalityIntermediateInclusion … (QuotientGroup.mk l')`.
2. By Mathlib's `QuotientGroup.eq` (`(a : α ⧸ s) = b ↔ a⁻¹ * b ∈ s`) and
   `Subgroup.mem_subgroupOf`, the goal becomes
   `((k'⁻¹ * l' : K'.toSubgroup) : G) ∈ L.toSubgroup`.
3. The map computes on representatives by definition (`QuotientGroup.map`
   of `Subgroup.inclusion hK'K`), so `QuotientGroup.eq.mp h` already has
   the stated type of `hmem`: the product
   `(Subgroup.inclusion hK'K k')⁻¹ * Subgroup.inclusion hK'K l'` lies in
   `L.toSubgroup.subgroupOf K.toSubgroup`. `Subgroup.mem_subgroupOf` turns
   this into membership of its underlying element of `G` in `L.toSubgroup`.
4. The inclusion does not change underlying elements, so after `simpa`
   normalizes the coercions of products, inverses and inclusions to `G`,
   `hG` closes the goal.

No auxiliary declaration, extra hypothesis, instance or `simp` registration
is introduced, and the proof does not use the M071.002 computation lemma:
the computation is definitional. The development check reports only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

### Adaptation: extension-subgroup membership

The source states the normality instances and `hmem` for
`CyclicCohomology.extensionSubgroup K L h` (M004.002), which abbreviates
`L.toSubgroup.subgroupOf K.toSubgroup`, and rewrites membership with
`KummerTheory.mem_extensionSubgroup_iff K L h k :
k ∈ extensionSubgroup K L h ↔ (k : G) ∈ L` (M022.001, source
`Nyll/GaloisCohomology/Kummer/Abstract/KummerAbelianAssembly.lean`,
lines 33–38, proof `Iff.rfl`). Neither is in the Library, and the published
statement uses the expanded Mathlib term. The port writes the expanded
subgroup in `hmem` and uses Mathlib's `Subgroup.mem_subgroupOf :
h ∈ H.subgroupOf K ↔ (h : G) ∈ H` at the two source uses (lines 80 and
86–88), with arguments implicit instead of the source's explicit
`K' L hLK' (k'⁻¹ * l')` and `K L (hLK'.trans hK'K) (…)`. The two lemmas
state the same equivalence for the same subgroup, so the proof steps are
unchanged.

## Actual dependencies

- The published proposition
  `Langlands.NYLL.ClassFormation.transferNormNaturalityIntermediateInclusion_injectiveStatement`
  in `Construction/MainTransfer/Intermediate/Statements` (unfolded only).
- The published definitions
  `Langlands.NYLL.ClassFormation.transferNormNaturalityIntermediateInclusion`
  (`MainTransfer/Intermediate/Definitions`) and
  `Langlands.NYLL.ClassFormation.finiteReciprocityNaturalityRestriction`
  (`MainNaturality/Restriction/Definitions`), reached through the unchanged
  import chain.
- Mathlib's `QuotientGroup.induction_on`, `QuotientGroup.eq`,
  `QuotientGroup.map`, `Subgroup.inclusion`, `Subgroup.mem_subgroupOf` and
  default `simp` lemmas on subgroup coercions.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainTransfer.lean:64–89`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainTransfer.lean#L64-L89).
Lines 64–65 are the retained docstring, 66–73 the signature and conclusion,
and 74–89 the tactic proof retained above. The inclusion is defined at
lines 35–45 (M071.001). The universe `u` is declared at line 16 and the
section variables `{G : Type u} [Group G] [TopologicalSpace G]` at line 32,
both retained. The whole-file SHA-256 is
`8885a9e7a8660d6e445083d71d2e8f188336aa4909fbb3d24b6624fadc2fef3e`,
recomputed by Worker 9 on 13 November 2026 UTC from the retained snapshot.

| Original in `ClassFormation` | Adapted in `Langlands.NYLL.ClassFormation` |
| --- | --- |
| Asserted type of `transferNormNaturalityIntermediateInclusion_injective` (M071.003) | Published `transferNormNaturalityIntermediateInclusion_injectiveStatement` in `Intermediate/Statements` |
| Proof `transferNormNaturalityIntermediateInclusion_injective` | This theorem of the same adapted name in `Intermediate/U003/Proofs` |
| `transferNormNaturalityIntermediateInclusion` (M071.001) | Existing published definition in `Intermediate/Definitions` |
| `KummerTheory.mem_extensionSubgroup_iff` (M022.001) | Mathlib `Subgroup.mem_subgroupOf` |
| `extensionSubgroup K L h` (M004.002) | Its Mathlib body `L.toSubgroup.subgroupOf K.toSubgroup` |

The adaptation prefixes the namespace with `Langlands.NYLL`, replaces the
original imports by the sole published `Intermediate/Statements` import,
states the theorem's type as the published proposition applied to
`K K' L hLK' hK'K`, and makes the membership replacements above. The
[public partition](../../../../../../../../../notes/reuse/nyll-public-port/m049-m072.md#m071)
places this proof at M071.003 after M071.002.END; no patch10 edit applies
to M071.

The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including "Naganori Yamaguchi
(assisted by OpenAI Codex)", followed by Worker 9's dated modification
record. Worker 9 extracted this proof directly from the pinned original
and the published statement. No unpublished project draft was reused, and
there are no project coauthors.

The unchanged inherited [LICENSE](../../../../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) are retained, with
SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`
respectively.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`:
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Development compilation is separate from acceptance. Publication under
`lean.proof@1` requires the Lake build, kernel and exact-target checks,
unchanged statement and dependency checks, independent semantic review and
Integrator publication.

This proof covers only M071.003. The representative computation
(M071.002), the image subgroup (M071.004) and the transfer, Frobenius and
norm-naturality results of M071 and any host reciprocity theorem are
separate work.
