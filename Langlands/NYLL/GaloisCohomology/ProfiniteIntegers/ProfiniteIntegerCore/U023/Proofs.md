# Density of the integers in the profinite-integer closure model

This module proves the independently published closed proposition
`Langlands.NYLL.ClassFormation.denseRange_intCast_zHatStatement`
by the theorem
`Langlands.NYLL.ClassFormation.denseRange_intCast_zHat`.
The theorem's type is exactly that proposition. The target has no
parameters, so there are no binders to apply and no universe parameter.

Its sole direct import is
`Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.Statements`.
That published Lean/Markdown pair and its complete imported chain, in
particular `ProfiniteIntegerCore.Definitions`, remain unchanged. The proof
uses only their existing constructions and Mathlib.

## Target and mathematical meaning

`Statements.lean` lines 49–50 define the target as

```lean
DenseRange (Int.castRingHom ZHat)
```

Here `ZHat : Type 0` is the inherited source model
(`Definitions.lean` line 70). It is the closed subring `d007`, the
topological closure of the diagonal integer subring `d006`, inside the
ambient product `d004 = ∀ i : d001, ZMod i.modulus` over all positive
moduli `i`. The diagonal ring map `d005 : ℤ →+* d004` sends `a` to the
family of its residue classes `(a : ZMod i.modulus)`, and `d006` is its
range (`Definitions.lean` lines 36–58). The ring structure `d009` and the
topology `d010` on `ZHat` are those of the closure subtype, transported by
`change` (`Definitions.lean` lines 74–82); the ambient product carries the
product of the discrete topologies on the finite rings `ZMod n`.

The assertion is that the image of the ordinary integer cast
`ℤ → ZHat` is dense for this actual subspace topology: every nonempty open
subset of `ZHat` contains the cast of some integer. No other topology,
host model or comparison with Mathlib's profinite completions is involved.

## Implemented proof

The theorem is on `Proofs.lean` line 35 and its tactic proof on lines
36–60. It follows the original
route, with the private source names replaced by their published support
names (see the declaration map below). It has four steps.

1. `hinclusion` (lines 36–42). The inclusion
   `Set.inclusion (Subring.le_topologicalClosure d006)` of the integer
   subring into its closure has dense range. By Mathlib's
   `denseRange_inclusion_iff`, this is the inclusion of the carrier of
   `d006.topologicalClosure` into `closure (d006 : Set d004)`. That carrier
   is by definition this closure, so the `change` on lines 40–41 states the
   goal as `closure ↑d006 ⊆ closure ↑d006`, closed by `Set.Subset.rfl`.
2. `hdiagonal` (lines 43–44). The range restriction
   `d005.rangeRestrict : ℤ → d005.range` is surjective
   (`RingHom.rangeRestrict_surjective`), hence has dense range
   (`Function.Surjective.denseRange`). Its codomain `d005.range` is `d006`.
3. `hcomp` (lines 45–50). If an outer map is continuous with dense range
   and an inner map has dense range, their composite has dense range
   (`DenseRange.comp`). Here the outer map is the inclusion, continuous by
   `continuous_inclusion`, and the inner map is `d005.rangeRestrict`.
   Hence the composite `ℤ → d007` has dense range.
4. `heq` and conclusion (lines 51–60). The composite equals
   `fun a : ℤ => Int.castRingHom ZHat a`. By function extensionality,
   `Subtype.ext`, and extensionality on the ambient product, it suffices
   that both sides have the same coordinate at each index `i`. Both are
   definitionally `(a : ZMod i.modulus)`: on the left by the definition of
   `d005`, on the right because the integer cast in the closure subring is
   computed in the ambient product of rings coordinatewise. So `rfl`
   closes each coordinate. Rewriting `hcomp` with `heq` gives density of
   the cast map. Its topology is the closure subtype topology, which is
   definitionally the instance `d010` on `ZHat`, so `exact hcomp` closes
   the goal.

No additional hypothesis, instance, simp registration or auxiliary
declaration is introduced. The development check reported no errors or
warnings and only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact source passage is
[`Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteIntegerCore.lean:169–196`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteIntegerCore.lean#L169-L196).
Line 169 is the retained docstring, lines 170–171 the signature, lines
172–178 the inclusion step, 179–180 the diagonal step, 181–186 the
composite, 187–194 the extensionality identity, and lines 195 and 196 the
closing `rw [heq] at hcomp` and `exact hcomp`. (The task context cites
lines 169–195; the final tactic `exact hcomp` is on line 196.) The
whole-file SHA-256 is
`a6cdc6d3cfca209257868daa4e1aa09ca4f83d08927114958d2737b93b309ae5`.
Worker 65 read the complete retained original file and recomputed its hash
on 13 November 2026 UTC.

| Original in `ClassFormation` | Adapted in `Langlands.NYLL` |
| --- | --- |
| Asserted type of `denseRange_intCast_zHat` | Published `ClassFormation.denseRange_intCast_zHatStatement` (`Statements.lean` 49–50) |
| Proof `denseRange_intCast_zHat` | This theorem `ClassFormation.denseRange_intCast_zHat` in U023.Proofs |
| private `ZHatAmbient` | `PortInternal.M008.d004` |
| private `zHatDiagonal` | `PortInternal.M008.d005` |
| private `zHatIntegerSubring` | `PortInternal.M008.d006` |
| private `ZHatClosureModel`, `ZHat` and its anonymous instances | `PortInternal.M008.d007`, `ClassFormation.ZHat`, `PortInternal.M008.d009`–`d014` |

The adaptation prefixes the namespace with `Langlands.NYLL`, replaces the
original imports by the sole published `Statements` import, opens
`PortInternal.M008` and uses `d004`, `d005` and `d006` where the source
uses its private names. The theorem is stated with the published closed
proposition as its type instead of the source's inline
`DenseRange (Int.castRingHom ZHat)`; the two are definitionally equal and
the source tactic script runs unchanged against it. Every source tactic
step is retained verbatim apart from these renamings. The other source
declarations of the file are omitted. The
[public partition](../../../../../../notes/reuse/nyll-public-port/m001-m024.md#m008)
places this proof at M008.023 after M008.022.END. No patch10 edit applies
to M008. The proof does not use M008.019–022 or M008.024.

The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Both source-ID errata paths under `notes/errata/` were checked in the
workspace, project and supplied Library on 13 November 2026 UTC; all six
paths were absent.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including “Naganori Yamaguchi
(assisted by OpenAI Codex)”, followed by Worker 65's dated modification
record. Worker 65 authored this proof extraction and companion directly
from the pinned original and the published statement and definitions.
No unpublished project draft or patch10 edit was reused. There are no
project coauthors for this pair.

The unchanged inherited [LICENSE](../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../licenses/NYLL/NOTICE), including applicable
dependency attribution, are retained in `repository_paths`. Their SHA-256
values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
matching the pinned originals.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`:
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Upstream used Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Development compilation is
separate from acceptance. Publication under `lean.proof@1` requires the
Lake/kernel/exact-target and unchanged-statement/frozen-dependency checks,
independent semantic review, and Integrator publication.

This proof covers only M008.023, density of the integer cast in the actual
Type-zero closure model. It asserts no comparison with a host or Mathlib
profinite completion and no reciprocity result. M008.019–022, M008.024 and
later NYLL units are separate work. Parent task
`457f00a2-e3a8-49c5-ac1c-07336dacb1b5` (Task 5264) retains its remaining
obligations.
