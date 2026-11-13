# NYLL M024.008: the relative norm value is fixed by the base subgroup

This module proves the published Library proposition
`Langlands.NYLL.ClassFormation.relativeNormValue_fixedStatement`
by the theorem `Langlands.NYLL.ClassFormation.relativeNormValue_fixed`.
The theorem's type is exactly that proposition applied to its source
parameters, `relativeNormValue_fixedStatement A K L hLK a k`, with the
finite coset-type instance supplied by elaboration.

Its sole direct import is
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.Statements`
(see [Statements.md](../Statements.md)). That published Lean/Markdown pair
and its complete imported chain remain unchanged. In particular the proof
does not import or restate the M024.002 and M024.004 theorems
`relativeCosetAction_mk` and `leftMulCosetEquiv_mk`.

## Target and parameters

The theorem has, in this order, implicit `G : IntegralRepGroupType` (the published alias of `Type 0`),
the instances `[Group G]` and `[TopologicalSpace G]`, explicit
`A : Rep ℤ G`, `K L : ClosedSubgroup G` and
`hLK : L.toSubgroup ≤ K.toSubgroup`, the instance
`[Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))]`, then
explicit `a : ambientFixedAddSubgroup A L` and `k : K.toSubgroup`, the
statement's telescope with the same binder kinds. The representation
carrier contributes the statement's single universe parameter. No premise
is added: only the relative coset type is assumed finite, with no
normality of `L` in `K`, no topological-group or continuity assumption.
Unfolding the proposition gives

```lean
A.ρ k.1 (relativeNormValue A K L hLK a) =
  relativeNormValue A K L hLK a
```

The published M024.005 `relativeNormValue A K L hLK a` is the sum, over all
left cosets `q` of `L.toSubgroup.subgroupOf K.toSubgroup` in `K.toSubgroup`
(with the `Fintype` structure `Fintype.ofFinite` of the finite instance), of
`relativeCosetAction A K L hLK a q`, the action on `a` of any representative
of `q`. The assertion says that this coset sum is fixed by `k`.

## Implemented proof

The complete proof body is

```lean
  unfold relativeNormValue_fixedStatement
  let := Fintype.ofFinite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))
  have hterm : ∀ q : K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup),
      A.ρ k.1 (relativeCosetAction A K L hLK a q) =
        relativeCosetAction A K L hLK a
          (leftMulCosetEquiv (L.toSubgroup.subgroupOf K.toSubgroup) k q) := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro x
    change A.ρ k.1 (A.ρ x.1 a.1) = A.ρ (k.1 * x.1) a.1
    rw [map_mul]
    rfl
  rw [relativeNormValue]
  simp_rw [map_sum, hterm]
  exact (leftMulCosetEquiv (L.toSubgroup.subgroupOf K.toSubgroup) k).sum_comp
    (relativeCosetAction A K L hLK a)
```

The `unfold` exposes the displayed equation, and the `let` fixes the same
`Fintype.ofFinite` structure that the definition of `relativeNormValue` uses.

The auxiliary fact `hterm` says that acting by `k` on the term of a coset
`q` gives the term of the coset `k q`, where `k q` is the published M024.003
permutation `leftMulCosetEquiv` (left multiplication by `k`) of the
relative coset type. By quotient induction `q` is the class of a
representative `x : K.toSubgroup`. The left side then reduces definitionally
to `A.ρ k.1 (A.ρ x.1 a.1)` (the M024.002 computation), and the right side to
`A.ρ (k.1 * x.1) a.1`, because left multiplication by `k` sends the class of
`x` to that of `k * x` (the M024.004 computation) and the subgroup product
coerces to `k.1 * x.1`. The `change` states exactly this. Rewriting with
`map_mul` turns `A.ρ (k.1 * x.1)` into the composite `A.ρ k.1 * A.ρ x.1`,
whose evaluation at `a.1` is definitionally the left side, so `rfl` closes it.

For the main goal, `rw [relativeNormValue]` unfolds the norm value on both
sides to the coset sum. `map_sum` moves the additive map `A.ρ k.1` inside the
sum, and `hterm` rewrites each term, so the left side becomes the sum over
all `q` of `relativeCosetAction A K L hLK a (leftMulCosetEquiv _ k q)`.
Since `leftMulCosetEquiv _ k` is a permutation of the finite coset type,
Mathlib's `Equiv.sum_comp` (reindexing a finite sum along an equivalence)
identifies this with the original sum, which closes the goal.

The original proof (lines 121–136) has exactly these steps, with one more:
before its `change` at line 130, it calls
`simp only [relativeCosetAction_mk, leftMulCosetEquiv_mk]` (line 129) to
reach the representative form. That step is dropped here: the `change`
already reaches the same goal by definitional reduction, so the proof needs
neither the unpublished M024.002 and M024.004 proofs nor local copies of
them.

## Pinned source and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Norm.lean`, whose
whole-file SHA-256
`5d57e3b5f1941fc987fefea159ad4686bb5f934319d6662c436b917bdbbf8578`
Worker 165 recomputed from the retained copy under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`
on 13 November 2026 UTC; it matches the
[port partition](../../../../../../../notes/reuse/nyll-public-port/m001-m024.md#m024),
which records no patch10 edit for M024.
The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL erratum note exists under `notes/errata/` in the
Library at commit `9b849caba7c63ede041b7fec49c90ceaafb08568`.

The passage is
[lines 113–136](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Norm.lean#L113-L136):
docstring at line 113, theorem name and telescope at 114–118, equation at
119–120 and proof at 121–136. The enclosing context is namespace
`ClassFormation` (line 22), `noncomputable section` (line 29) and the
section variables at line 34.

| Original in `ClassFormation` | Adapted in `Langlands.NYLL.ClassFormation` |
| --- | --- |
| Asserted type of `relativeNormValue_fixed` | Published `relativeNormValue_fixedStatement` |
| Proof `relativeNormValue_fixed` | This theorem, same adapted name |
| `CyclicCohomology.extensionSubgroup K L hLK` | Its exact body `L.toSubgroup.subgroupOf K.toSubgroup`, as in the statement |
| `relativeCosetAction`, `leftMulCosetEquiv`, `relativeNormValue` | Existing published data (M024.001, .003, .005) |
| `ambientFixedAddSubgroup` | Existing published data (M023.001) |

Modifications by Worker 165 on 13 November 2026 UTC: prefix the namespace
with `Langlands.NYLL`; replace the source imports with the sole Statements
import; give the theorem the published proposition applied to its
parameters as its type and unfold it first; write every occurrence of
`extensionSubgroup K L hLK` as the published `Subgroup.subgroupOf` body;
drop the `simp only [relativeCosetAction_mk, leftMulCosetEquiv_mk]` step;
omit the source `noncomputable section`, `open CyclicCohomology` and all
other source declarations. The original docstring and all other proof steps
are retained.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including “Naganori Yamaguchi
(assisted by OpenAI Codex)”, followed by Worker 165's dated modification
record. Worker 165 extracted this proof directly from the pinned original
and the published statement; no project draft was reused and there are no
project coauthors. The statement pair and its definitions (Worker 200)
are imported unchanged; no imported Library file is edited.

The unchanged inherited [LICENSE](../../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../../licenses/NYLL/NOTICE) are retained in
`repository_paths`. Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`:
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Upstream used Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. A development `lean_check`
compiled the module with no errors or warnings, and declaration
inspection reported only the axioms `propext`, `Classical.choice` and
`Quot.sound`, with the single universe parameter of the statement.
Development compilation is separate from acceptance: publication under
`lean.proof@1` also requires the Lake, kernel and exact-target checks,
independent semantic review and Integrator publication.

This proof covers only M024.008. It supplies the fixedness used by the
`relativeNorm` definition M024.009, which, like the other M024 units and
every host class-formation, cup, transfer, Tate or reciprocity target,
remains separate work.
