# Nondegenerate modules as direct limits

Worker 258. This proof module proves the published `Langlands.Algebra.NondegenerateModuleDirectLimitStatement`, Renard (9 July 2026), I.1.2, printed page 7 / PDF page 13. The registered source is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

Cofinality moves any idempotent fixing a vector into the filtering system. The forward universal property uses the directed additive-subgroup gluing lemma with the fixed subgroups `e.leftImage M`.

For the converse, quotient the additive group by its nondegenerate part. Each additive character of this quotient into the rational circle, composed with the quotient map and lifted to the prescribed test universe, vanishes on every `e.leftImage M`. Uniqueness in the universal property forces it to be zero. Mathlib's character-separation theorem then forces every quotient class to vanish, so every vector belongs to the nondegenerate part. This is an internal proof of the published statement; the character argument handles the independent universe of test groups.
