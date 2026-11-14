# Abelianized restriction on quotient representatives: proof

This module proves the published closed proposition
`Langlands.NYLL.ClassFormation.normResidueNaturalityAbelianizedRestriction_of_mkStatement`
(NYLL source unit M086.020) by the theorem
`Langlands.NYLL.ClassFormation.normResidueNaturalityAbelianizedRestriction_of_mk`.
Its only import is the statement module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Main.U020.Statements`,
which imports the definition module `Reciprocity.Main.U019.Definitions`
(M086.019). The statement pair and everything it imports are unchanged.

## Exact target

The theorem has one universe parameter `u` and its type is exactly
`normResidueNaturalityAbelianizedRestriction_of_mkStatement.{u}`. Unfolded,
it says:

```lean
∀ {G : Type u} [Group G] [TopologicalSpace G]
  (K K' L L' : ClosedSubgroup G)
  (hLK : L.toSubgroup ≤ K.toSubgroup)
  (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
  (hK'K : K'.toSubgroup ≤ K.toSubgroup)
  (hL'L : L'.toSubgroup ≤ L.toSubgroup)
  [(Langlands.NYLL.CyclicCohomology.extensionSubgroup K L hLK).Normal]
  [(Langlands.NYLL.CyclicCohomology.extensionSubgroup K' L' hL'K').Normal]
  (k' : K'.toSubgroup),
  normResidueNaturalityAbelianizedRestriction K K' L L'
      hLK hL'K' hK'K hL'L
      (Abelianization.of (QuotientGroup.mk k')) =
    Abelianization.of
      (QuotientGroup.mk (Subgroup.inclusion hK'K k'))
```

In words: the abelianized restriction map `G(L'/K')ᵃᵇ → G(L/K)ᵃᵇ` sends
the class of `k' ∈ K'` to the class of `k'` viewed in `K`.

## Proof

After introducing the binders:

1. `change` rewrites the left side by unfolding
   `normResidueNaturalityAbelianizedRestriction` (which is
   `Abelianization.map (finiteReciprocityNaturalityRestriction …)`) to
   Mathlib's definitional form
   `Abelianization.lift (Abelianization.of.comp (finiteReciprocityNaturalityRestriction …))`.
2. `rw [Abelianization.lift_apply_of]` evaluates the lift on
   `Abelianization.of (QuotientGroup.mk k')`, leaving
   `Abelianization.of (finiteReciprocityNaturalityRestriction … (QuotientGroup.mk k'))`.
3. `rfl` closes the goal: the published restriction map is
   `QuotientGroup.map` along `Subgroup.inclusion hK'K`, which sends the
   class of `k'` to the class of `Subgroup.inclusion hK'K k'` by definition.

The proof has the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Original correspondence

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Main.lean`
(SHA-256
`6883a1db96a9baf23b9c4f040e635f10b7732f36c558d9e0a96faa88a2da854b`),
theorem `ClassFormation.normResidueNaturalityAbelianizedRestriction_of_mk`:
docstring lines 1043–1047, `@[simp]` line 1048, signature lines 1049–1063,
proof lines 1064–1071.

Adaptation changes:

- The theorem gets the `Langlands.NYLL` namespace prefix and proves the
  published closed proposition instead of carrying the binders in its
  signature. The proof therefore starts with `intro`.
- After the `intro`, the tactic proof (`change`, `rw [Abelianization.lift_apply_of]`,
  `rfl`) is the original one.
- The source `@[simp]` attribute is not installed.
- The single import replaces the original imports. All other declarations
  of the source module are omitted. The source docstring is kept.

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Attribution

The Lean header keeps the original 2026 Naganori Yamaguchi copyright,
authorship line and Apache-2.0 notice, followed by a dated modification
record by Worker 56. The retained
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are unchanged.

No instance or simp attribute is installed. The development check reports
no errors or warnings.

Worker 677 adopted Worker 56's shared revision 1 for Task 6396 on
14 November 2026, checked the proof against the pinned original, and
submitted the unchanged Lean proof with Worker 56 credited as coauthor.
