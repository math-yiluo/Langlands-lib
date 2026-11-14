# The principal correction unit attached to a positive ideal power

For a in the n-th maximal-ideal power with 1 ≤ n, choose the unit of the valuation ring supplied by the published invertibility proof for 1 + a. The paired proposition states that its valuation-ring value is 1 + a.

## Pinned source and attribution

Naganori Yamaguchi (assisted by OpenAI Codex), `n-yamaguchi-0729/ClassFieldTheory`, commit `fbd320cd8b1b06487c58227e92eb135794267709`, `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitQuotients.lean`. Registered original `external-lean-reuse-snapshots-2026-10-21`, content fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The retained original file SHA-256 is `6147c6613cd0176ace8787d7c65a3026d23bd5e23dc3282902d5ea66a0977c83`. The readable snapshot is `/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

The original copyright/Apache-2.0/author header is retained in the Lean file. The unchanged original license and notices are `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`. Worker 194 made the extraction and adaptations recorded below on 14 November 2026.

## Exact source correspondence

| Source unit and lines | Original declaration | Published declaration |
| --- | --- | --- |
| M132.072, 961–964 | `LocalFieldTheory.principalUnitOneAddOfMemPow` | `Langlands.NYLL.LocalFieldTheory.principalUnitOneAddOfMemPow` |
| M132.073, 968–972 | `LocalFieldTheory.principalUnitOneAddOfMemPow_val` | `Langlands.NYLL.LocalFieldTheory.principalUnitOneAddOfMemPow_valStatement` |

Line ranges include each complete original declaration and any original proof; only its signature and proposition are retained for a statement target. The definition names above denote the constructions themselves. The statement names above denote propositions, without proofs of those propositions.

## Telescope, construction and modifications

Retain (K : Type u), [Field K], [ValuativeRel K], implicit {n : Nat}, explicit hn, a and ha in precisely the source order. No topology or nonarchimedean-local-field class is added. The construction is exactly (isUnit_one_add_of_mem_maximalIdeal_pow K hn a ha).unit, using the published source-adapted M132.071 proof; there is no substitute choice of unit. The source @[simp] theorem becomes an ordinary Prop-valued definition and receives no simp attribute; its proof IsUnit.unit_spec is omitted from this statement-only part.

The source namespace is adapted to the namespace displayed in the name table. Original whole-module imports are replaced by these focused imports:

- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.U071.Proofs`

Each theorem is changed to a `def` returning `Prop`: the full ordered telescope is retained, and the source conclusion becomes its body. Source theorem proofs and theorem attributes are omitted. Construction bodies and any proof terms inside them are unchanged apart from resolving source names to their published adaptations. Documentation comments are replaced with focused unit labels; unrelated source declarations and unused opens are omitted. No new global or local instance is declared. These support units assert no host class-formation, cup, transfer, Tate or reciprocity comparison.

## Lean declarations

The following is the exact authored declaration content, in its declared namespace and context.

```lean
noncomputable section

universe u

open scoped ValuativeRel

/-- Source M132.072: original construction. -/
noncomputable def principalUnitOneAddOfMemPow
    (K : Type u) [Field K] [ValuativeRel K] {n : Nat} (hn : 1 ≤ n)
    (a : 𝒪[K]) (ha : a ∈ (𝓂[K] ^ n : Ideal 𝒪[K])) : 𝒪[K]ˣ :=
  (isUnit_one_add_of_mem_maximalIdeal_pow K hn a ha).unit

/-- Source M132.073: exact proposition target. -/
def principalUnitOneAddOfMemPow_valStatement
    (K : Type u) [Field K] [ValuativeRel K] {n : Nat} (hn : 1 ≤ n)
    (a : 𝒪[K]) (ha : a ∈ (𝓂[K] ^ n : Ideal 𝒪[K])) : Prop :=
    ((principalUnitOneAddOfMemPow K hn a ha : 𝒪[K]ˣ) : 𝒪[K]) = 1 + a
```
