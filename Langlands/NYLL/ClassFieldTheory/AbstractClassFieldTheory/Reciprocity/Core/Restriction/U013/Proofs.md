# NYLL M075.013: finiteness of the lower extension

This module proves the published Library proposition
`Langlands.NYLL.ClassFormation.abstractReciprocity_lowerExtension_finiteStatement`
by the theorem
`Langlands.NYLL.ClassFormation.abstractReciprocity_lowerExtension_finite`.
The theorem's type is exactly that proposition applied to its source
parameters, `abstractReciprocity_lowerExtension_finiteStatement K M L hLM hMK`,
with the implicit group, its two structures and the finiteness instance
supplied by elaboration.

Its sole direct import is
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core.Restriction.Statements`.
That published Lean/Markdown pair and its complete imported chain remain
unchanged.

## Target and parameters

The theorem has, in this order, implicit `G : Type u_1`, the instances
`[Group G]` and `[TopologicalSpace G]`, explicit closed subgroups
`K M L : ClosedSubgroup G`, explicit `hLM : L.toSubgroup ≤ M.toSubgroup`
and `hMK : M.toSubgroup ≤ K.toSubgroup`, and the named instance
`hLfinite : Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)`.
The universe is arbitrary. As in the source, there are no normality
hypotheses: the quotients are Mathlib's left-coset types, and no group
structure on them is used.

Unfolding the published proposition gives

```lean
Finite (M.toSubgroup ⧸ L.toSubgroup.subgroupOf M.toSubgroup)
```

that is, `L` has finitely many left cosets in `M`, given that it has
finitely many left cosets in `K`. Neither `G`, `K` nor `M` is assumed
finite.

## Implemented proof

The complete proof body is

```lean
  let inclusion :
      (M.toSubgroup ⧸ L.toSubgroup.subgroupOf M.toSubgroup) →
        (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) :=
    Quotient.map' (Subgroup.inclusion hMK) (by
      intro x y hxy
      rw [QuotientGroup.leftRel_apply] at hxy ⊢
      apply Subgroup.mem_subgroupOf.2
      simpa using Subgroup.mem_subgroupOf.1 hxy)
  apply Finite.of_injective inclusion
  intro x y
  refine QuotientGroup.induction_on x ?_
  intro m
  refine QuotientGroup.induction_on y ?_
  intro n h
  apply QuotientGroup.eq.mpr
  apply Subgroup.mem_subgroupOf.2
  have h' :
      (QuotientGroup.mk (Subgroup.inclusion hMK m) :
          K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) =
        QuotientGroup.mk (Subgroup.inclusion hMK n) := by
    simpa [inclusion] using h
  have hmem := QuotientGroup.eq.mp h'
  have hG := Subgroup.mem_subgroupOf.1 hmem
  simpa using hG
```

1. **The coset map.** `inclusion` sends the left coset of `m : M` modulo
   `L` to the left coset of `Subgroup.inclusion hMK m : K` modulo `L`. It is
   built with `Quotient.map'` from Mathlib's subgroup inclusion
   `Subgroup.inclusion hMK : M.toSubgroup →* K.toSubgroup`. Well-definedness:
   by `QuotientGroup.leftRel_apply`, related representatives `x, y : M`
   satisfy `x⁻¹ * y ∈ L.toSubgroup.subgroupOf M.toSubgroup`, and the goal is
   `(Subgroup.inclusion hMK x)⁻¹ * Subgroup.inclusion hMK y ∈
   L.toSubgroup.subgroupOf K.toSubgroup`.
   `Subgroup.mem_subgroupOf` turns both memberships into membership of the
   underlying elements of `G` in `L.toSubgroup`, namely of `↑(x⁻¹ * y)` and
   of `↑((Subgroup.inclusion hMK x)⁻¹ * Subgroup.inclusion hMK y)`; once `simpa` normalizes the
   coercions of products, inverses and inclusions to `G`, the hypothesis
   closes the goal.
2. **Reduction to injectivity.** Mathlib's `Finite.of_injective` states that
   the domain of an injective function into a finite type is finite. The
   codomain is finite by `hLfinite`, and `apply` unifies the conclusion
   `Finite (M.toSubgroup ⧸ L.toSubgroup.subgroupOf M.toSubgroup)` with the
   published proposition by unfolding its `def`. It remains to show that
   `inclusion` is injective.
3. **Injectivity.** By `QuotientGroup.induction_on` twice, take cosets of
   `m, n : M` with equal images `h`. By `QuotientGroup.eq` (Mathlib's
   `(a : α ⧸ s) = b ↔ a⁻¹ * b ∈ s`) and `Subgroup.mem_subgroupOf`, the goal
   becomes `↑(m⁻¹ * n) ∈ L.toSubgroup`. The hypothesis `h`, after unfolding
   `inclusion` on representatives by `simp`, is the equality `h'` of the
   cosets of `Subgroup.inclusion hMK m` and `Subgroup.inclusion hMK n`
   modulo `L` in `K`; by
   `QuotientGroup.eq` and `Subgroup.mem_subgroupOf` this gives
   `↑((Subgroup.inclusion hMK m)⁻¹ * Subgroup.inclusion hMK n) ∈
   L.toSubgroup`, which `simpa` identifies with the goal since the subgroup
   inclusion does not change underlying elements of `G`.

No auxiliary declaration, extra hypothesis, instance or `simp` registration
is introduced; `inclusion` is a local `let`. The development check reports
only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

### Adaptation: extension-subgroup membership

The source proof uses `KummerTheory.mem_extensionSubgroup_iff K L h k :
k ∈ extensionSubgroup K L h ↔ (k : G) ∈ L` (M022.001, source
`Nyll/GaloisCohomology/Kummer/Abstract/KummerAbelianAssembly.lean`,
lines 33–38, proof `Iff.rfl`), where
`CyclicCohomology.extensionSubgroup K L h` (M004.002) abbreviates
`L.toSubgroup.subgroupOf K.toSubgroup`. Neither is in the Library, and the
published statement already uses the expanded Mathlib term. The port
therefore uses Mathlib's `Subgroup.mem_subgroupOf :
h ∈ H.subgroupOf K ↔ (h : G) ∈ H` at each of the four source uses
(lines 634, 635, 643 and 650–651), with its arguments implicit instead of
the source's explicit `K L h x`. The two lemmas state the same equivalence
for the same subgroup, so the proof steps are unchanged; the explicit
element argument of the source call at lines 650–651 is recovered by
unification with `hmem`.

## Actual dependencies

- The published proposition
  `Langlands.NYLL.ClassFormation.abstractReciprocity_lowerExtension_finiteStatement`
  in `Core/Restriction/Statements` (unfolded only).
- Mathlib's `Quotient.map'`, `Subgroup.inclusion`,
  `QuotientGroup.leftRel_apply`, `Subgroup.mem_subgroupOf`,
  `Finite.of_injective`, `QuotientGroup.induction_on`, `QuotientGroup.eq`
  and default `simp` lemmas on subgroup coercions, reached through the
  import chain.

The restriction map of M075.005 and the other M075 proofs are not used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Core.lean:619–652`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Core.lean#L619-L652).
Line 619 is the retained docstring, 620–627 the signature and conclusion,
and 628–652 the tactic proof retained above. The section variable
`{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` at line 454 is
shadowed by the declaration's own `{G : Type*}` binder and is omitted. The
whole-file SHA-256 is
`0fc1bd5c66d628b74e079fd54af4a9df7334343e38186983257da5ce6a8f06fb`,
recomputed by Worker 9 on 13 November 2026 UTC from the retained snapshot.

| Original in `ClassFormation` | Adapted in `Langlands.NYLL.ClassFormation` |
| --- | --- |
| Asserted type of `abstractReciprocity_lowerExtension_finite` (M075.013) | Published `abstractReciprocity_lowerExtension_finiteStatement` in `Core/Restriction/Statements` |
| Proof `abstractReciprocity_lowerExtension_finite` | This theorem of the same adapted name in `Core/Restriction/U013/Proofs` |
| `KummerTheory.mem_extensionSubgroup_iff` (M022.001) | Mathlib `Subgroup.mem_subgroupOf` |
| `extensionSubgroup K L h` (M004.002) | Its Mathlib body `L.toSubgroup.subgroupOf K.toSubgroup` |

The adaptation prefixes the namespace with `Langlands.NYLL`, replaces the
original imports by the sole published `Core/Restriction/Statements` import,
states the theorem's type as the published proposition applied to
`K M L hLM hMK`, and makes the membership replacements above. The
[public partition](../../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m075)
places this proof at M075.013 after M075.012.END; no patch10 edit applies
to M075. This proof does not depend on M075.010–012.

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

This proof covers only M075.013. The restriction lemmas (M075.006–009),
the upper-row inclusion and exactness (M075.010–012), the norm-subgroup
comparisons and any host class-formation, transfer or reciprocity theorem
are separate work.
