# NYLL M243.022: the decomposition group stabilizes the maximal ideal

This module proves the theorem
`Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup_maximalIdeal_stabilizer_eq_top`,
whose type is the published closed target
`decompositionGroup_maximalIdeal_stabilizer_eq_topStatement.{u, v}` of the module
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.Statements`
(explained in the [statement Markdown](Statements.md)). It is the proof unit of the source
theorem M243.022 of the
[NYLL port inventory](../../../../../../notes/reuse/nyll-public-port/m241-m258.md#m243).

## Target

```lean
theorem decompositionGroup_maximalIdeal_stabilizer_eq_top :
    decompositionGroup_maximalIdeal_stabilizer_eq_topStatement.{u, v}
```

The target is the `def`

```lean
∀ (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
  (A : _root_.ValuationSubring L),
  MulAction.stabilizer (decompositionGroup K A)
      (IsLocalRing.maximalIdeal A) = ⊤
```

for an arbitrary field extension `L / K` (no Galois hypothesis) and valuation subring `A`
of `L`. The decomposition group `decompositionGroup K A` (M239.001) acts on `A` through
Mathlib's `ValuationSubring.decompositionSubgroupMulSemiringAction`
(`Mathlib/RingTheory/Valuation/RamificationGroup.lean`, line 40), and hence on the ideals of
`A` by Mathlib's pointwise action `Ideal.pointwiseMulSemiringAction`
(`Mathlib/RingTheory/Ideal/Pointwise.lean`, line 59, made an instance in the scope
`Pointwise` at line 64), where `σ • I` is the ideal `Ideal.map` of `I` along the ring map
`x ↦ σ • x`. So the target says: every element of the
decomposition group maps the maximal ideal `𝔪_A` of `A` onto itself.

## Implemented proof

```lean
intro K L _ _ _ A
apply top_unique
intro sigma _hsigma
change sigma • IsLocalRing.maximalIdeal A = IsLocalRing.maximalIdeal A
apply Ideal.ext
intro x
rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
simp only [IsLocalRing.mem_maximalIdeal]
constructor
· intro hnonunit hx
  apply hnonunit
  simpa using hx.map (MulSemiringAction.toRingAut
    (decompositionGroup K A) A sigma⁻¹)
· intro hnonunit hx
  apply hnonunit
  simpa using hx.map (MulSemiringAction.toRingAut
    (decompositionGroup K A) A sigma)
```

The module has `open scoped Pointwise`, so that the action on ideals is available to the
`change` and the rewrite. The steps are:

1. `intro` introduces the closed telescope. The `def` target unfolds when `intro` needs a
   binder.
2. `apply top_unique` (`Mathlib/Order/BoundedOrder/Basic.lean`, line 173: `⊤ ≤ a → a = ⊤`)
   reduces the equation to `⊤ ≤ MulAction.stabilizer _ (IsLocalRing.maximalIdeal A)`.
3. For `sigma` in `⊤`, membership of `sigma` in the stabilizer is by definition the equation
   `sigma • 𝔪_A = 𝔪_A`, which `change` states.
4. `Ideal.ext` reduces it to `x ∈ sigma • 𝔪_A ↔ x ∈ 𝔪_A` for every `x : A`.
5. `Ideal.mem_pointwise_smul_iff_inv_smul_mem` (`Pointwise.lean`, line 133) rewrites the left
   side to `sigma⁻¹ • x ∈ 𝔪_A`.
6. `IsLocalRing.mem_maximalIdeal` (`Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean`,
   line 31) rewrites membership in `𝔪_A` to membership in `nonunits A`, which by definition
   is `¬ IsUnit _`. The goal is `sigma⁻¹ • x ∈ nonunits A ↔ x ∈ nonunits A`.
7. In each direction, `intro` takes the non-unit hypothesis `hnonunit` and a unit hypothesis
   `hx` for the other element, and `apply hnonunit` leaves the claim that the first element
   is a unit. This follows by applying to `hx` the ring automorphism of `A` given by `sigma⁻¹`
   (forward) or `sigma` (backward), namely `MulSemiringAction.toRingAut _ A` evaluated there
   (`Mathlib/Algebra/Ring/Action/End.lean`, line 61), with `IsUnit.map`
   (`Mathlib/Algebra/Group/Units/Hom.lean`, line 208). `simpa` identifies the image with the
   required element. In a development check, `simpa?` reported that the forward step uses the
   simp lemmas `MulSemiringAction.toRingAut_apply`, `map_inv`, `RingAut.inv_apply` and
   `MulSemiringAction.toRingEquiv_apply_symm_apply`, and the backward step uses
   `MulSemiringAction.toRingAut_apply`, `MulSemiringAction.toRingEquiv_apply_apply` and
   `smul_inv_smul` (so `sigma • sigma⁻¹ • x` becomes `x`).

The source theorem has no private helper, so no private source lemma is used or inlined. The
proof uses no property of `decompositionGroup K A` beyond its action on `A` by ring
automorphisms.

## Dependencies

- `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.Statements`: the target and, through the published M243 and M239 data modules and their
  Mathlib imports, the actions and the lemmas named above. No other module is imported.

## Source correspondence and modifications

The source theorem is [`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean`, lines 250–272](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean#L250-L272):

```lean
omit [IsGalois K L] in
/-- Every decomposition-group automorphism stabilizes the maximal ideal of
the selected valuation ring. -/
theorem decompositionGroup_maximalIdeal_stabilizer_eq_top
    (A : _root_.ValuationSubring L) :
    MulAction.stabilizer (decompositionGroup K A)
        (IsLocalRing.maximalIdeal A) = ⊤ := by
  apply top_unique
  intro sigma _hsigma
  change sigma • IsLocalRing.maximalIdeal A = IsLocalRing.maximalIdeal A
  apply Ideal.ext
  intro x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [IsLocalRing.mem_maximalIdeal]
  constructor
  · intro hnonunit hx
    apply hnonunit
    simpa using hx.map (MulSemiringAction.toRingAut
      (decompositionGroup K A) A sigma⁻¹)
  · intro hnonunit hx
    apply hnonunit
    simpa using hx.map (MulSemiringAction.toRingAut
      (decompositionGroup K A) A sigma)
```

| Source | Adapted |
| --- | --- |
| `omit [IsGalois K L] in` | Not needed: the target has no `[IsGalois K L]` binder and the module has no section variables |
| `theorem decompositionGroup_maximalIdeal_stabilizer_eq_top (A) : MulAction.stabilizer (decompositionGroup K A) (IsLocalRing.maximalIdeal A) = ⊤` | `theorem decompositionGroup_maximalIdeal_stabilizer_eq_top : decompositionGroup_maximalIdeal_stabilizer_eq_topStatement.{u, v}` |
| Tactic proof | `intro`, then the source tactic proof unchanged |
| Docstring | Kept verbatim |

The source context `open scoped Pointwise Topology` (line 37) is reduced to
`open scoped Pointwise`, which the proof needs; `Topology` is not used. The source imports
are replaced by the import listed above and `noncomputable section` is not reproduced. The
namespace `RamificationTheory.HilbertRamification.ValuationSubring` gets the prefix
`Langlands.NYLL`, and `universe u v` is kept. The section variables
`(K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]` and the theorem's own binder
`(A : _root_.ValuationSubring L)` are the leading binders of the published closed target,
introduced by `intro`, with the same names, order and binder kinds. No global instance is
registered: the source declaration is a theorem.

## Development check

In the approved environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), `lean_check` built this module over the
workspace's Library base `c40a01345b2f4172fa41e07ff31644b40e695003` with no errors and no
warnings. Inspection found a theorem with level parameters `u`, `v` using only the axioms
`propext`, `Classical.choice` and `Quot.sound`. This check is not independent review
or publication.

## Attribution and license

The original copyright and author header (copyright 2026 Naganori Yamaguchi, author
“Naganori Yamaguchi (assisted by OpenAI Codex)”, released under Apache-2.0) is kept
verbatim at the top of the Lean file, followed in the same comment by Worker 173's dated
modification record. The pinned original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, retained in the registered sources
`external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`) and
`nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`). The whole source file
(461 lines) was read; its SHA-256 is
`cf543e2e441798c17d1b7b07167e0508d629b6ed143c66b624c04889f0b5927e`, as recorded in the
statement Markdown. The unchanged [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are byte-identical to the retained
originals, with SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. No Mathlib code is copied into this file.
Worker 121's published statement and the imported data modules are used unchanged; all
imported Library modules and their paired Markdown remain frozen.

## Scope

This module proves only M243.022. It adds no other declaration. It does not construct the
homomorphism `decompositionGroupToMaximalIdealStabilizer` from the decomposition group to the
stabilizer (M243.023), which uses this theorem, or the residue action.
