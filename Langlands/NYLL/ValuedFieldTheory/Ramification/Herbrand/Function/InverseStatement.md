# Finite inverse Herbrand laws statement

This module extracts the seven theorem signatures M303.030–.034 and
M303.036–.037 from Naganori Yamaguchi's *ClassFieldTheory (NYLL)*,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/Ramification/Herbrand/Function.lean`,
lines 355–408](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/Herbrand/Function.lean#L355-L408).
The original file has SHA-256
`668006f8122da36b9bd34657988f9d0d6164a629ea10feb340002f2317c40580`.
Its imports, ambient telescope and local instances at lines 1–70 and
the surrounding continuity, inverse and order-isomorphism passage at
lines 335–408 were read directly.

## Complete closed proposition

The sole declaration is
`Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.HerbrandInverseLawsStatement`.
Its complete source is the following within the indicated namespace:

```lean
universe u

namespace Langlands.NYLL.RamificationTheory.DiscreteValuationField
namespace AntitoneNormalSubgroupFiltration

def HerbrandInverseLawsStatement : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] (F : AntitoneNormalSubgroupFiltration G),
    (∀ t : ℝ, herbrandFunction F (inverseHerbrandFunction F t) = t) ∧
    (∀ s : ℝ, inverseHerbrandFunction F (herbrandFunction F s) = s) ∧
    StrictMono (inverseHerbrandFunction F) ∧
    Function.Surjective (inverseHerbrandFunction F) ∧
    Continuous (inverseHerbrandFunction F) ∧
    (∀ s : ℝ, herbrandFunction F s ∈ Set.Ici (-1) ↔ s ∈ Set.Ici (-1)) ∧
    (∀ t : ℝ, inverseHerbrandFunction F t ∈ Set.Ici (-1) ↔ t ∈ Set.Ici (-1))

end AntitoneNormalSubgroupFiltration
end Langlands.NYLL.RamificationTheory.DiscreteValuationField
```

The constant has type `Prop`, with the sole universe parameter `u`.
It has no external term parameters. Its defining proposition internally
quantifies an arbitrary group `G : Type u`, a supplied `Group G`
instance, a supplied `Finite G` instance, and every supplied antitone
normal subgroup filtration `F` of `G`. Each real variable is quantified
inside its corresponding conjunct. In particular, the final two
equivalences are separate universally quantified clauses.

Writing `φ = herbrandFunction F` and `ψ = inverseHerbrandFunction F`,
the seven conjuncts assert, in order:

1. `φ (ψ t) = t` for every real `t`.
2. `ψ (φ s) = s` for every real `s`.
3. `ψ` is strictly increasing on the real line.
4. `ψ` is surjective onto the real line.
5. `ψ` is continuous on the real line.
6. `φ s ∈ [-1, ∞)` if and only if `s ∈ [-1, ∞)`, for every real `s`.
7. `ψ t ∈ [-1, ∞)` if and only if `t ∈ [-1, ∞)`, for every real `t`.

The forward function is the published normalized
[`herbrandFunction`](Definitions.md): its slope on `(m, m+1)` is
`|F.lower (m+1)| / |F.lower 0|`, and it is the identity below zero.
The published [`inverseHerbrandFunction`](InverseDefinition.md) is
`Function.invFun (herbrandFunction F)`. These definitions and their
documentation are imported unchanged.

All seven laws retain their original finite-group scope. Neither the
strict monotonicity nor surjectivity of either function, nor either
inverse identity, continuity or interval equivalence, is a premise.
The only internally supplied data are the group, its group and
finiteness instances, and the filtration. There is no eventual-triviality
condition or arithmetic data.

## Exact source map and extraction

All original declarations below are in
`RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration`.
Each adapted entry is the indicated conjunct of the fully qualified
`HerbrandInverseLawsStatement` above; this module introduces no
individual theorem under the original suffix.

| Unit | Original declaration suffix and signature lines | Adapted conjunct |
| --- | --- | --- |
| M303.030 | `herbrandFunction_inverseHerbrandFunction`, 356–357 | 1: `∀ t : ℝ, herbrandFunction F (inverseHerbrandFunction F t) = t` |
| M303.031 | `inverseHerbrandFunction_herbrandFunction`, 361–362 | 2: `∀ s : ℝ, inverseHerbrandFunction F (herbrandFunction F s) = s` |
| M303.032 | `inverseHerbrandFunction_strictMono`, 366 | 3: `StrictMono (inverseHerbrandFunction F)` |
| M303.033 | `inverseHerbrandFunction_surjective`, 372 | 4: `Function.Surjective (inverseHerbrandFunction F)` |
| M303.034 | `continuous_inverseHerbrandFunction`, 377 | 5: `Continuous (inverseHerbrandFunction F)` |
| M303.036 | `herbrandFunction_mem_Ici_neg_one_iff`, 391–392 | 6: `∀ s : ℝ, herbrandFunction F s ∈ Set.Ici (-1) ↔ s ∈ Set.Ici (-1)` |
| M303.037 | `inverseHerbrandFunction_mem_Ici_neg_one_iff`, 399–400 | 7: `∀ t : ℝ, inverseHerbrandFunction F t ∈ Set.Ici (-1) ↔ t ∈ Set.Ici (-1)` |

The namespace gains `Langlands.NYLL`. Seven signatures become a single
right-associated conjunction under one internal universal telescope.
The source's explicit real arguments in the first two signatures and
implicit real arguments in the last two signatures become explicit
universal quantifiers inside their own conjuncts. The ambient
`[Finite G]` is retained for every clause. The two original local
subgroup instances are proof support and are omitted from this
statement extraction.

The module imports
`Langlands.NYLL.ValuedFieldTheory.Ramification.Herbrand.Function.InverseDefinition`
for the existing generic functions and filtration, and
`Mathlib.Topology.MetricSpace.Pseudo.Defs` for the standard real
topology. These focused imports replace the source's arithmetic,
cardinality, floor, order-continuity and ramification imports.
No analytic proof module is needed to formulate the proposition.
The redundant source `noncomputable section` is omitted: defining
this proposition does not compute either noncomputable function.

The published source partition records no patch10 change for M303.
Its source-order edges are scheduling guidance. The intervening
M303.035 `herbrandOrderIso` is separate data and is not required to
express these signatures. This module supplies a statement target;
its proof, an order-isomorphism construction, actual unique-extension
laws, upper-group laws and reciprocity conclusions remain separate.

## Sources, license and authorship

The registered source is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/` followed by the
original path above. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No workspace, project or supplied-Library `notes/errata` directory
was present at preparation.

The original copyright and author header is retained verbatim:
copyright 2026 Naganori Yamaguchi, all rights reserved; authors Naganori
Yamaguchi (assisted by OpenAI Codex). Apache-2.0 applies. The existing
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) match the pinned
originals, with SHA-256 values respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Their inherited notices remain unchanged. The root NOTICE inventory
has no entry for this source file.

Worker 106 contributed the source/interface extraction, reuse analysis
and closed-target design. Worker 1199 checked the pinned source,
published dependencies and licenses, implemented the extraction and
wrote this companion on 2 November 2026. The Lean header records the
changes. The approved environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`, distinct from upstream Lean
4.35.0-rc2 with Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.
