# NYLL M074.012: the order of the Galois quotient of a finite extension

This module proves the published Library proposition
`Langlands.NYLL.ClassFormation.additiveExtensionQuotient_cardStatement`
by the theorem
`Langlands.NYLL.ClassFormation.additiveExtensionQuotient_card`.
The theorem's type is exactly that proposition applied to its source
parameter, `additiveExtensionQuotient_cardStatement E`. It has no universe
parameters: the group `G` ranges over `IntegralRepGroupType`, as in the
statement module.

Its only direct import is
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.CyclicNormQuotient.ClassFieldAxiomCard.Statements`
(the target). The statement's Lean/Markdown pair and its complete imported
chain remain unchanged.

## Target and parameters

The theorem has the single explicit parameter
`E : DegreeData.FiniteAbstractExtension G`; the section variables are
`{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]`.

A finite abstract extension `E` bundles closed subgroups `E.field` and
`E.base` of `G` with `E.below : E.field.toSubgroup ≤ E.base.toSubgroup` and
a proof that the coset space
`E.base.toSubgroup ⧸ E.field.toSubgroup.subgroupOf E.base.toSubgroup`
is finite. Its published degree `E.degree : ℕ+` has underlying natural
number `Nat.card E.quotient`, where `E.quotient` is that coset space. The
published abbreviation `extensionSubgroup E.base E.field E.below` is
`E.field.toSubgroup.subgroupOf E.base.toSubgroup`. Unfolding the target
gives

`Nat.card (Additive (E.base.toSubgroup ⧸ extensionSubgroup E.base E.field E.below)) =
  (E.degree : ℕ)`.

## Implemented proof

The file first proves a private auxiliary lemma

```lean
private theorem additiveExtensionQuotient_card_index_eq_degree
    (E : DegreeData.FiniteAbstractExtension G) :
    (extensionSubgroup E.base E.field E.below).index = (E.degree : ℕ) := by
  rw [Subgroup.index]
  rfl
```

which is the statement of the unpublished M010.092
`FiniteAbstractExtension.extensionSubgroup_index_eq_degree`, with the
extension subgroup written through the abbreviation `extensionSubgroup`.
After unfolding `Subgroup.index`, the goal
`Nat.card (E.base.toSubgroup ⧸ extensionSubgroup E.base E.field E.below) =
(E.degree : ℕ)` holds by `rfl`, because the published `E.degree` is built
from `Nat.card E.quotient` and `E.quotient` is, by definition, the same
coset space.

The main proof is the source calc chain:

1. `Nat.card_congr` applied to the equivalence `Additive.ofMul` between the
   quotient and its additive form, read backwards, identifies
   `Nat.card (Additive Q)` with `Nat.card Q` for
   `Q = E.base.toSubgroup ⧸ extensionSubgroup E.base E.field E.below`.
2. Mathlib's `Subgroup.index_eq_card`, read backwards, identifies
   `Nat.card Q` with the index of `extensionSubgroup E.base E.field E.below`.
3. The auxiliary lemma identifies that index with `(E.degree : ℕ)`.

No other auxiliary declaration, hypothesis, instance or `simp`
registration is introduced. The development check reports only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

### Adaptations

- **M010.092.** The source's last calc step cites
  `E.extensionSubgroup_index_eq_degree`. The port cites the private lemma
  above instead. The source proof of M010.092 is
  `rw [Subgroup.index, E.degree_coe]; rfl`
  (`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`,
  lines 780–785), where `degree_coe : (E.degree : ℕ) = Nat.card E.quotient`
  is M010.088 (lines 749–752), whose own source proof is `rfl`. The private
  lemma drops the rewrite by the unpublished M010.088 and closes the goal
  by `rfl` directly, which is the same definitional unfolding. Its private
  name does not conflict with the adapted name of M010.092, which this
  module does not declare.
- The source theorem's conclusion is replaced by the published
  proposition applied to `E`; the calc chain is unchanged, since `calc`
  checks its composed relation against the unfolded target.
- `open CyclicCohomology` makes `extensionSubgroup` available, as in the
  statement module.

## Actual dependencies

- The published proposition `additiveExtensionQuotient_cardStatement`
  (unfolded only) in `Reciprocity/CyclicNormQuotient/ClassFieldAxiomCard/Statements`.
- The published structure `DegreeData.FiniteAbstractExtension` and its
  definitions `quotient`, `subgroup` and `degree`
  (`Degree/Fields/FiniteExtension/Definitions`), and the published
  abbreviation `CyclicCohomology.extensionSubgroup`
  (`GaloisCohomology/Cyclic/NormKernelVanishing/Extension/Definitions`),
  reached through the unchanged import chain.
- Mathlib's `Nat.card_congr`, `Additive.ofMul`, `Subgroup.index` and
  `Subgroup.index_eq_card`.

The unpublished M010.088 and M010.092 are not used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/CyclicNormQuotient.lean:457–483`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/CyclicNormQuotient.lean#L457-L483).
Line 457 is the docstring, 458–464 the signature and conclusion, and
464–483 the calc proof retained above (the partition's unit M074.012 spans
lines 458–486, up to the next declaration). The enclosing context is
`namespace ClassFormation` (line 21), `open KummerTheory` and
`open CyclicCohomology` (lines 23 and 25), `noncomputable section`
(line 29), `open CategoryTheory` (line 31) and
`variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]`
(line 34). The whole-file SHA-256 values of the retained snapshot files,
recomputed by Worker 746 on 16 November 2026 UTC, are:

| File | SHA-256 |
| --- | --- |
| `Reciprocity/CyclicNormQuotient.lean` | `6dc5f10e7546a7b85d7712388b443344fe87679ef13d0eadb0f3451f925c731a` |
| `Degree/Fields.lean` | `841b30407b1f9f3eb64a30f6ccfa4f8ec555c791564a7e682b7c8ee23c2d156e` |

| Original in `ClassFormation` | Adapted in `Langlands.NYLL.ClassFormation` |
| --- | --- |
| Asserted type of `additiveExtensionQuotient_card` (M074.012) | Published `additiveExtensionQuotient_cardStatement` |
| Proof `additiveExtensionQuotient_card` | This theorem of the same adapted name in `ClassFieldAxiomCard/U012/Proofs` |
| `E.extensionSubgroup_index_eq_degree` (M010.092) | Private `additiveExtensionQuotient_card_index_eq_degree` |
| `E.degree_coe` (M010.088), used inside M010.092 | Definitional `rfl` |

The [public partition](../../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m074)
places this proof at M074.012.

The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including "Naganori Yamaguchi
(assisted by OpenAI Codex)", followed by Worker 746's dated modification
record. Worker 746 extracted this proof directly from the pinned original
and the published statement. No unpublished project draft was reused, and
there are no project coauthors.

The unchanged inherited [LICENSE](../../../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are retained, with
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

This proof covers only M074.012. The published proofs of M010.088 and
M010.092, the rest of M074 and any reciprocity theorem are separate work.
