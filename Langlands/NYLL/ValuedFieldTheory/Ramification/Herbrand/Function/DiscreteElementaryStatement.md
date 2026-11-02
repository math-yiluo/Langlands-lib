# Elementary slope and natural-sum laws of the Herbrand function: statement

This module defines the closed proposition
`Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.HerbrandDiscreteElementaryStatement`.
It conjoins the signatures of the eight elementary theorems M303.005–.012
from Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/Ramification/Herbrand/Function.lean`, lines 55–109](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/Herbrand/Function.lean#L55-L109),
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The complete source file has SHA-256
`668006f8122da36b9bd34657988f9d0d6164a629ea10feb340002f2317c40580`.
Source lines 1–130 were read, including the section variables, the two
definitions and all eight theorems with their proofs.

This module publishes the proposition only. It does not assert that any
conjunct has been proved. A separate exact-target proof unit is expected to
establish it, and the proposition takes none of its eight conclusions as a
premise.

## Complete proposition

The module imports only the published
`Langlands.NYLL.ValuedFieldTheory.Ramification.Herbrand.Function.Definitions`.
In the namespace
`Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration`,
the complete definition is:

```lean
universe u

def HerbrandDiscreteElementaryStatement : Prop :=
  (∀ {G : Type u} [Group G] (F : AntitoneNormalSubgroupFiltration G),
    herbrandValueNat F 0 = 0 ∧
    ∀ n : ℕ, herbrandValueNat F (n + 1) = herbrandValueNat F n + herbrandSlope F n) ∧
  (∀ {G : Type u} [Group G] [Finite G] (F : AntitoneNormalSubgroupFiltration G),
    (∀ i : ℕ, 0 < herbrandSlope F i) ∧
    (∀ i : ℕ, 0 ≤ herbrandSlope F i) ∧
    (∀ i : ℕ, (1 : ℝ) / Nat.card (F.lower 0) ≤ herbrandSlope F i) ∧
    (∀ n : ℕ, 0 ≤ herbrandValueNat F n) ∧
    (∀ n : ℕ, (n : ℝ) / Nat.card (F.lower 0) ≤ herbrandValueNat F n) ∧
    StrictMono (herbrandValueNat F))
```

The declaration has type `Prop`, its only universe parameter is the
arbitrary `u`, and it has no value parameters. The proposition is a
conjunction of two universally quantified blocks, in this order:

- **Block 1** quantifies an implicit group carrier `{G : Type u}`, a supplied
  instance `[Group G]` and an explicit filtration
  `(F : AntitoneNormalSubgroupFiltration G)`. It has no `Finite G`, `Fintype`
  or other premise. Its body is the two-conjunct conjunction of the vanishing
  law and the successor law.
- **Block 2** separately quantifies `{G : Type u}`, `[Group G]`,
  `[Finite G]` and `(F : AntitoneNormalSubgroupFiltration G)`, in this order.
  Its body is the six-conjunct conjunction of the positivity, lower-bound and
  monotonicity laws.

The group, instance and filtration binders of the two blocks are separate
universal binders inside the closed proposition; both groups live in the same
arbitrary universe `u`. No arithmetic extension, valuation, Galois group,
enumeration of the group, eventual-triviality cutoff, normalization of the
initial subgroup or termination hypothesis occurs.

## Reused definitions and their conventions

The statement uses exactly the published definitions of
[`Definitions`](Definitions.md), unchanged:

```lean
noncomputable def herbrandSlope
    {G : Type u} [Group G] (F : AntitoneNormalSubgroupFiltration G)
    (i : ℕ) : ℝ :=
  (Nat.card (F.lower (i + 1)) : ℝ) / Nat.card (F.lower 0)

noncomputable def herbrandValueNat
    {G : Type u} [Group G] (F : AntitoneNormalSubgroupFiltration G)
    (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (herbrandSlope F) i
```

`F.lower` is the subgroup family of the published generic
[`AntitoneNormalSubgroupFiltration`](../../GaloisValuation/RamificationQuotients/Filtration.md)
structure, which has no eventual-triviality field. `Nat.card (F.lower 0)` is
Mathlib's `Nat.card` of the actual subgroup carrier type `↥(F.lower 0)`, the
order of the zeroth subgroup. In conjuncts (3) and (5) of block 2 it is cast
to `ℝ` by the natural-number cast, and the division is real division. In
conjunct (5), `(n : ℝ)` is the natural-number cast of the index. The zeros
are of two kinds. The right-hand side of the vanishing law
`herbrandValueNat F 0 = 0` and the zeros compared with `herbrandSlope F i` in
conjuncts (1) and (2) and with `herbrandValueNat F n` in conjunct (4) of
block 2 are real numbers. The index zeros, the argument of
`herbrandValueNat F 0` and the `0` in `F.lower 0`, are natural numbers,
because `herbrandValueNat F` and `F.lower` take natural-number arguments.
`herbrandValueNat F 0` is the empty finite sum, and `n + 1` is natural-number
addition. `StrictMono (herbrandValueNat F)` is
Mathlib's `∀ ⦃a b : ℕ⦄, a < b → herbrandValueNat F a < herbrandValueNat F b`,
for the usual orders on `ℕ` and `ℝ`.

The statement introduces no new slope, sum, cardinality or filtration. Its
elaborated body mentions no `Fintype` or decidability instance: `Nat.card` is
defined for every type.

## Clause-by-clause source correspondence

All original names are in the source namespace
`RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration`,
opened at lines 33–34. The source section declares
`variable {G : Type u} [Group G] [Finite G]` at line 36 and
`variable (F : AntitoneNormalSubgroupFiltration G)` at line 37.
Each theorem has the docstring "States the theorem `name`." on the line before
its signature; M303.005 also carries `@[simp]`.

| Block, conjunct | Item | Original theorem | Lines (omit / docstring / signature / proof) | Original statement after `F` |
| --- | --- | --- | --- | --- |
| 1, first | M303.005 | `herbrandValueNat_zero` | 55 / 56 / 57 / 58 | `(herbrandValueNat F) 0 = 0` |
| 1, second | M303.006 | `herbrandValueNat_succ` | 60 / 61 / 62–64 / 65 | `(n : ℕ) : (herbrandValueNat F) (n + 1) = (herbrandValueNat F) n + (herbrandSlope F) n` |
| 2, (1) | M303.007 | `herbrandSlope_pos` | – / 67 / 68–69 / 70–72 | `(i : ℕ) : 0 < (herbrandSlope F) i` |
| 2, (2) | M303.008 | `herbrandSlope_nonneg` | – / 74 / 75–76 / 77 | `(i : ℕ) : 0 ≤ (herbrandSlope F) i` |
| 2, (3) | M303.009 | `one_div_card_le_herbrandSlope` | – / 79 / 80–81 / 82–86 | `(i : ℕ) : (1 : ℝ) / Nat.card (F.lower 0) ≤ (herbrandSlope F) i` |
| 2, (4) | M303.010 | `herbrandValueNat_nonneg` | – / 88 / 89–90 / 91 | `(n : ℕ) : 0 ≤ (herbrandValueNat F) n` |
| 2, (5) | M303.011 | `nat_div_card_le_herbrandValueNat` | – / 93 / 94–95 / 96–102 | `(n : ℕ) : (n : ℝ) / Nat.card (F.lower 0) ≤ (herbrandValueNat F) n` |
| 2, (6) | M303.012 | `herbrandValueNat_strictMono` | – / 104 / 105 / 106–109 | `StrictMono (herbrandValueNat F)` |

The task contract's line ranges 55–59 and 61–66 for the first two items
include the adjacent blank or docstring lines; the table gives the exact lines.
In words, the conjuncts are:

1. block 1, first: the natural Herbrand sum at `0` is `0`;
2. block 1, second: for every `n`, the sum at `n + 1` is the sum at `n` plus
   the slope at `n`;
3. block 2, (1): every slope is positive;
4. block 2, (2): every slope is nonnegative;
5. block 2, (3): every slope is at least `1 / |F.lower 0|`;
6. block 2, (4): the natural sum is nonnegative at every `n`;
7. block 2, (5): the natural sum at `n` is at least `n / |F.lower 0|`;
8. block 2, (6): the natural sum is strictly monotone in the index.

Each conjunct keeps its source direction and its source expressions.
`(herbrandValueNat F) 0` and `herbrandValueNat F 0` denote the same
application; the statement drops only these redundant parentheses.

## The two finiteness scopes

Lean 4 includes an instance-implicit section variable in a theorem when all
the variables it depends on are included. Since every theorem here mentions
`F`, and therefore `G` and `Group G`, the section's `[Finite G]` belongs to a
theorem's signature unless it is omitted. M303.005 and M303.006 are preceded
by `omit [Finite G] in` at lines 55 and 60. Their effective telescopes are
`{G : Type u} [Group G] (F : AntitoneNormalSubgroupFiltration G)`, followed by
`(n : ℕ)` for M303.006. This is block 1, which has no finiteness hypothesis.
Both laws are identities of finite prefix sums, valid for every group and
filtration.

M303.007–.012 have no `omit`. Their effective telescopes are
`{G : Type u} [Group G] [Finite G] (F : AntitoneNormalSubgroupFiltration G)`,
followed by `(i : ℕ)` or `(n : ℕ)` for M303.007–.011. This is block 2, which
keeps `[Finite G]` with the source binder order. Under this hypothesis each
`F.lower k` is a finite subgroup, nonempty since it contains `1`, so its
`Nat.card` is positive. The source proofs obtain positivity in exactly this
way, from `Finite.card_pos`. The real divisions in conjuncts (3) and (5) are
by the actual order of `F.lower 0`.

The hypothesis is not removable from block 2. `Nat.card` is `0` on an infinite
type, and real division by `0` gives `0`. For example, on the infinite group
`Multiplicative ℤ` the constant filtration at `⊤` has every slope
`0 / 0 = 0`, so conjunct (1) of block 2 fails, and its natural sum is
identically `0`, so conjunct (6) fails too. The local instances M303.001–.002
(lines 39–44) provide `Fintype` and membership decidability for subgroups.
They are separate declarations rather than section variables, and no
signature of M303.005–.012 mentions them.

## Organizational adaptations

Conjunction and closure are the only organizational adaptations:

- The eight theorem signatures become one conjunction, in source order.
- The two source finiteness scopes become two blocks. Each block quantifies
  its group, instances and filtration once around its conjunction. A
  universal quantifier over a conjunction is equivalent to the conjunction of
  the universally quantified clauses.
- The section variables become binders inside each block with their source
  binder information: `G` implicit, `Group G` and `Finite G` instance
  arguments, `F` explicit.
- The explicit index arguments `(n : ℕ)` and `(i : ℕ)` become the universal
  quantifiers `∀ n : ℕ` and `∀ i : ℕ` of their conjuncts. M303.005 and
  M303.012 have no index argument.

The statement keeps the shifted slope, normalized by the order of
`F.lower 0`, and the prefix sum over `i < n`. It does not reformulate the
laws with a different normalization, enumeration, cutoff or Herbrand
polygon. In particular, the existing
`Langlands.Ramification.Herbrand.polygon` and
`Langlands.Ramification.Padic.herbrandPhi` require cutoff or arithmetic data
and are not used.

## Proof boundary and module contents

The source proofs, at lines 58, 65, 70–72, 77, 82–86, 91, 96–102 and 106–109,
are omitted. This module contains no theorem proving any conjunct. The module
adds exactly one constant, the proposition definition, with no auxiliary
constant and no instance. It contains no `herbrandFunction` law, inverse
Herbrand function, order isomorphism, continuity or surjectivity statement,
upper-numbering, inertia or reciprocity assertion.

## Provenance, attribution and modifications

Worker 106 supplied the source extraction, the grouping of these eight laws,
the scope analysis and the exact two-block target design in the task
contract. Worker 1045 checked the formulation against the pinned original and
the published definitions, implemented the module and wrote this
documentation on 2 November 2026. The adaptation prefixes the namespace with
`Langlands.NYLL` and imports only the published `Definitions` module, which
supplies the definitions and, transitively, the Mathlib notions used here.
It conjoins the eight signatures into one closed proposition in two
finiteness blocks and names the declaration as requested. It omits the
proofs, the theorem docstrings, the `@[simp]` attribute, the `omit` commands,
the local subgroup instances and the noncomputable section. The source
hypotheses and conclusions have no mathematical change. The source partition
`notes/reuse/nyll-public-port/m289-m312.md` records no patch10 change for
M303.

The registered source is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
at `n-yamaguchi-0729--ClassFieldTheory/source/` followed by the source path
above. Its attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The supplement's verification manifest records the same SHA-256 for this
file, and its `files/Nyll/ValuedFieldTheory/ANTHROPIC_FLT_SOURCE.md` has no
entry for it. No applicable errata were found in the project, workspace or
current Library.

The original copyright and author header is retained in the Lean file:
copyright 2026 Naganori Yamaguchi (`https://github.com/n-yamaguchi-0729`), all
rights reserved; authors Naganori Yamaguchi (assisted by OpenAI Codex). The
source is released under Apache-2.0. The existing copies of
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) remain unchanged, including
the inherited notices and earlier-source credits. The Lean header records the
modifications.
