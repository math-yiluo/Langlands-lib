# The contracted maximal ideal is the maximal ideal of the fixed subring (NYLL M243.017)

This module proves the published proposition
`Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedMaximalIdeal_eq_maximalIdealStatement`
with the theorem
`Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedMaximalIdeal_eq_maximalIdeal`.
It imports the unchanged statement module
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.MaximalIdealStatement`
and the published Library module
`Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal`.

## Target and mathematical meaning

The theorem's type is exactly the closed proposition
`decompositionFixedMaximalIdeal_eq_maximalIdealStatement.{u, v}`. It has the two
universe parameters `u` and `v`, and its binders are the statement's own. For
every `K : Type u`, implicit `L : Type v`, `[Field K] [Field L] [Algebra K L]`,
`[IsGalois K L]` and `A : ValuationSubring L`:

`decompositionFixedMaximalIdeal K A = IsLocalRing.maximalIdeal (decompositionFixedSubring K A)`.

Mathematically, let `G_w` be the decomposition group of `A` over `K`, that is,
the `K`-automorphisms of `L` that preserve `A`. Let `A^{G_w}` be the subring of
`A` fixed by `G_w`. Pulling the maximal ideal of `A` back to `A^{G_w}` gives
exactly the maximal ideal of the local ring `A^{G_w}`. In the source, `A^{G_w}`
is the valuation ring of the decomposition field `Z_w`. The hypothesis
`[IsGalois K L]` is the source's. This proof does not use it, but it stays in
the statement, as the task requires.

## Implemented proof

The proof is two tactic steps. `intro K L _ _ _ _ A` introduces the closed
telescope. Then `exact` closes the goal with

`(FixedPoints.maximalIdeal_subring_eq_comap (R := A) (M := decompositionGroup K A)).symm`.

The published Library theorem `FixedPoints.maximalIdeal_subring_eq_comap` holds
for any commutative local ring `R` with a monoid `M` acting on it by a
`MulSemiringAction`. It says
`IsLocalRing.maximalIdeal (FixedPoints.subring R M) = Ideal.comap (FixedPoints.subring R M).subtype (IsLocalRing.maximalIdeal R)`.
Its proof shows that an element of the fixed subring is a unit there exactly
when it is a unit in `R`. Here `R` is `A`, a local ring because it is a
valuation subring, and `M` is the subgroup `decompositionGroup K A`, which acts
on `A` through the NYLL data. The NYLL names are abbreviations:
`decompositionFixedSubring K A` is `FixedPoints.subring A (decompositionGroup K A)`,
and `decompositionFixedMaximalIdeal K A` is
`(IsLocalRing.maximalIdeal A).comap (decompositionFixedSubring K A).subtype`.
So the reversed equation is the goal up to unfolding these definitions, and
`exact` accepts it.

On the right-hand side, the `IsLocalRing (decompositionFixedSubring K A)`
instance is the Library's global instance `FixedPoints.isLocalRing_subring`.
The statement uses the same instance, from the same module. This module adds no
auxiliary declaration, instance, simp attribute or option. It needs no private
helper.

## Pinned source and modifications

Source: Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean:208–216`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean#L208-L216).
The docstring is at lines 208–209 and the theorem at line 210. The section
variables are at lines 39–40.

| Original (namespace `RamificationTheory.HilbertRamification.ValuationSubring`) | Adapted |
| --- | --- |
| Theorem `decompositionFixedMaximalIdeal_eq_maximalIdeal`, lines 210–215 | This theorem, with the same name under `Langlands.NYLL.` |
| Section variables `K`, `{L}`, field, algebra and `[IsGalois K L]` instances, and explicit `A` (lines 39–40, 211) | Bound in the published closed statement at universes `u v` |
| Conclusion, lines 212–213 | `decompositionFixedMaximalIdeal_eq_maximalIdealStatement.{u, v}` |
| Proof term `IsLocalRing.eq_maximalIdeal (decompositionFixedMaximalIdeal.instIsMaximal (K := K) A)`, lines 214–215 | `intro`, then the reversed `FixedPoints.maximalIdeal_subring_eq_comap` |
| Docstring, lines 208–209 | Unchanged |

The source proof uses the maximality instance M243.016, whose own proof needs
the profinite and integrality machinery of lines 179–206. The adapted proof
replaces it with the generic fixed-subring comparison. That comparison is
already in the Library, so M243.016 and its prerequisites are not needed here.
Other adaptations: the namespace gains the `Langlands.NYLL` prefix. The source
imports are replaced by the two published modules named above. The theorem is
stated as the closed published proposition, not over section variables. The
`noncomputable section`, the `open scoped Pointwise Topology` and the module
documentation of the whole source file are omitted. A short module docstring
for this result is added.

The [port partition](../../../../../../notes/reuse/nyll-public-port/m241-m258.md#m243)
lists this unit as `M243.017` (source line 210, `B0:S→P`).

## Attribution, licence and environment

The Lean file keeps the original 2026 Naganori Yamaguchi copyright, Apache-2.0
and author header verbatim, including "Naganori Yamaguchi (assisted by OpenAI
Codex)". Worker 133's dated modification record follows it. The proof route is
the one the task context names. Worker 133 wrote and checked this module, and
there are no project coauthors. The unchanged inherited
[LICENSE](../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are already
in the Library and are not modified. The reused module
`Def_Mathlib_RingTheory_Invariant_FixedSubringLocal` is a published Library
module that carries its own Anthropic FLT Apache-2.0 attribution. It is
imported, not copied.

The pinned source is registered as `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`).
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
Worker 133 recomputed the SHA-256 of the whole source file on 14 November 2026
UTC: `cf543e2e441798c17d1b7b07167e0508d629b6ed143c66b624c04889f0b5927e`.

The development environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`). There the module
compiles with no errors or warnings. The theorem has universe parameters `u v`
and depends only on `propext`, `Classical.choice` and `Quot.sound`. Compilation
is not acceptance. Publication under `lean.proof@1` also requires the Lake
build, the exact-target and unchanged-statement checks, independent semantic
review and integration.
