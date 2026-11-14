# Cardinality and exactness targets for integral ModuleCat morphisms

The three propositions assert equality of range cardinalities under conjugacy, multiplicative exactness of the tagged additive maps, and the product-of-range-cardinalities identity for an exact pair with finite middle term. Each uses the actual ModuleCat morphism, its underlying linear map and additive homomorphism, and the multiplicative type tag.

## Pinned source and attribution

Naganori Yamaguchi (assisted by OpenAI Codex), `n-yamaguchi-0729/ClassFieldTheory`, commit `fbd320cd8b1b06487c58227e92eb135794267709`, `Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Cardinality.lean`. Registered original `external-lean-reuse-snapshots-2026-10-21`, content fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The retained original file SHA-256 is `2757f501b1f901072b2292af5db735cc54db7f11b2403c3354a37f82fdda8226`. The readable snapshot is `/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

The original copyright/Apache-2.0/author header is retained in the Lean file. The unchanged original license and notices are `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`. Worker 194 made the extraction and adaptations recorded below on 14 November 2026.

## Exact source correspondence

| Source unit and lines | Original declaration | Published declaration |
| --- | --- | --- |
| M117.014, 281–290 | `CyclicCohomology.ProfiniteCohomology.Herbrand.moduleCatRangeCard_eq_of_conjugate` | `Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.moduleCatRangeCard_eq_of_conjugateStatement` |
| M117.015, 294–310 | `CyclicCohomology.ProfiniteCohomology.Herbrand.mulExact_of_moduleCat_exact` | `Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.mulExact_of_moduleCat_exactStatement` |
| M117.017, 327–339 | `CyclicCohomology.ProfiniteCohomology.Herbrand.moduleCat_card_eq_card_range_mul_card_range_of_exact` | `Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.moduleCat_card_eq_card_range_mul_card_range_of_exactStatement` |

Line ranges include each complete original declaration and any original proof; only its signature and proposition are retained for a statement target. The definition names above denote the constructions themselves. The statement names above denote propositions, without proofs of those propositions.

## Telescope, construction and modifications

All objects remain ModuleCat.{0} ℤ; there is no new universe generalization. M117.014 keeps implicit X/Y/X'/Y', explicit f/g/eX/eY and the explicit conjugacy hypothesis h, even though h is unused in the proposition body. M117.015 keeps implicit X/Y/Z, explicit f/g and hexact. M117.017 has the same order followed by the source [Finite Y] instance after hexact. Ambient G/A/B/C and group/action instances are unused by these source statements and are not source declaration parameters. Local unused-variable lint is disabled to retain the unused proof and finiteness binders. No source proof or moduleCatRangeEquivOfConjugate construction is imported or claimed.

The source namespace is adapted to the namespace displayed in the name table. Original whole-module imports are replaced by these focused imports:

- `Mathlib.Algebra.Category.ModuleCat.Basic`
- `Mathlib.Algebra.Exact.Basic`
- `Mathlib.Algebra.Group.TypeTags.Hom`
- `Mathlib.SetTheory.Cardinal.Finite`

Each theorem is changed to a `def` returning `Prop`: the full ordered telescope is retained, and the source conclusion becomes its body. Source theorem proofs and theorem attributes are omitted. Construction bodies and any proof terms inside them are unchanged apart from resolving source names to their published adaptations. Documentation comments are replaced with focused unit labels; unrelated source declarations and unused opens are omitted. No new global or local instance is declared. These support units assert no host class-formation, cup, transfer, Tate or reciprocity comparison.

## Lean declarations

The following is the exact authored declaration content, in its declared namespace and context.

```lean
open CategoryTheory

set_option linter.unusedVariables false

/-- Source M117.014: exact proposition target. -/
def moduleCatRangeCard_eq_of_conjugateStatement
    {X Y X' Y' : ModuleCat.{0} ℤ}
    (f : X ⟶ Y) (g : X' ⟶ Y')
    (eX : X ≅ X') (eY : Y ≅ Y')
    (h : eX.inv ≫ f ≫ eY.hom = g) : Prop :=
    Nat.card (MonoidHom.range
        f.hom.toAddMonoidHom.toMultiplicative) =
      Nat.card (MonoidHom.range
        g.hom.toAddMonoidHom.toMultiplicative)

/-- Source M117.015: exact proposition target. -/
def mulExact_of_moduleCat_exactStatement
    {X Y Z : ModuleCat.{0} ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hexact : Function.Exact f g) : Prop :=
    Function.MulExact
      f.hom.toAddMonoidHom.toMultiplicative
      g.hom.toAddMonoidHom.toMultiplicative

/-- Source M117.017: exact proposition target. -/
def moduleCat_card_eq_card_range_mul_card_range_of_exactStatement
    {X Y Z : ModuleCat.{0} ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hexact : Function.Exact f g) [Finite Y] : Prop :=
    Nat.card Y =
      Nat.card (MonoidHom.range
        f.hom.toAddMonoidHom.toMultiplicative) *
      Nat.card (MonoidHom.range
        g.hom.toAddMonoidHom.toMultiplicative)
```
