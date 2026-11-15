# Closedness of the reduction-modulo-`f` kernel of `d_K` (NYLL M301.004)

This module proves the published proposition
`Langlands.NYLL.ClassFormation.DegreeData.unramifiedDegreeKernelWithin_isClosedStatement`
by the theorem
`Langlands.NYLL.ClassFormation.DegreeData.unramifiedDegreeKernelWithin_isClosed`.
Its sole import is the statement module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ValuationContinuity.Statements`,
which is left unchanged (as is the definitions module
`...Reciprocity.ValuationContinuity.Definitions` it imports).

## Target and mathematical meaning

The theorem has implicit `G : Type u` (arbitrary universe `u`) with
`[Group G] [TopologicalSpace G]`, and explicit `D : DegreeData G`,
`K : FiniteResidueAbstractField D`, `f : ℕ` and `hf : 0 < f`, in this order.
There is no `IsTopologicalGroup G` hypothesis. Its type is
`unramifiedDegreeKernelWithin_isClosedStatement D K f hf`, which unfolds to

`IsClosed (unramifiedDegreeKernelWithin D K f hf : Set K.toSubgroup)`.

Mathematically: let `d_K : G_K → ℤ̂` be the normalized degree of the
finite-residue abstract field `K` (a continuous homomorphism on the field
subgroup `G_K = K.toSubgroup` with its subspace topology), and let
`unramifiedDegreeHom D K f hf : G_K →ₜ* Multiplicative (ZMod f)` be its
composite with reduction modulo `f`. Then the kernel
`unramifiedDegreeKernelWithin D K f hf` of this composite, the subgroup that
fixes the degree-`f` unramified extension, is a closed subset of `G_K`.

## Implemented proof

After `unfold unramifiedDegreeKernelWithin_isClosedStatement` the rest is the
unchanged source tactic proof:

1. `change` rewrites the goal to
   `IsClosed ((unramifiedDegreeHom D K f hf) ⁻¹' ({1} : Set (Multiplicative (ZMod f))))`.
   This holds by definitional unfolding: `unramifiedDegreeKernelWithin D K f hf`
   is by definition `(unramifiedDegreeHom D K f hf).toMonoidHom.ker`, and
   membership in a `MonoidHom.ker` is `φ x = 1`, which is membership in the
   preimage of `{1}`.
2. `isClosed_singleton.preimage (unramifiedDegreeHom D K f hf).continuous_toFun`
   closes it. A singleton is closed in the T1 space `Multiplicative (ZMod f)`.
   The `T1Space` instance comes from type-class search: Mathlib gives `ZMod f` the
   discrete topology (`Mathlib/Topology/Instances/ZMod.lean`) and `Multiplicative`
   keeps it (`Mathlib/Topology/Constructions.lean`). The preimage of a closed set
   under the continuous map underlying the bundled continuous homomorphism
   (`ContinuousMonoidHom.continuous_toFun`) is closed (`IsClosed.preimage`).

The proof does not use `hf` beyond its occurrence in the definitions. It adds no
auxiliary declaration, instance or simp attribute. Its only dependencies are the
imported NYLL definitions and Mathlib.

## Pinned source and declaration map

Source: Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/ValuationContinuity.lean:57–70`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/ValuationContinuity.lean#L57-L70)
(docstring lines 57–60, theorem lines 61–70), with section context at lines
22–36 (`noncomputable section`, `open scoped Topology`, `namespace ClassFormation`,
`open ClassFormation CyclicCohomology KummerTheory`, `universe u`,
`section DegreeOnly`, `variable {G : Type u} [Group G] [TopologicalSpace G]`,
`namespace DegreeData`).

| Original (namespace `ClassFormation.DegreeData`) | Adapted |
| --- | --- |
| Theorem `unramifiedDegreeKernelWithin_isClosed`, lines 61–70 | This theorem, same name under `Langlands.NYLL.` |
| Docstring, lines 57–60 | Identical |
| Binders `(D : DegreeData G) (K : FiniteResidueAbstractField D) (f : ℕ) (hf : 0 < f)` with section variables `{G : Type u} [Group G] [TopologicalSpace G]` | Identical, in the same order |
| Conclusion `IsClosed (unramifiedDegreeKernelWithin D K f hf : Set K.toSubgroup)` (lines 64–65) | `unramifiedDegreeKernelWithin_isClosedStatement D K f hf` |
| Tactic proof, lines 66–70 | Identical, preceded by one `unfold` |

Other adaptations: the `Langlands.NYLL` namespace prefix, and the single
statement import in place of the three source imports. The proof does not
use the source's `noncomputable section`, `open scoped Topology` or
`open ClassFormation CyclicCohomology KummerTheory`, so they are left out.

## Attribution, licence and environment

The Lean file keeps the original 2026 Naganori Yamaguchi copyright, Apache-2.0
and author header verbatim, including "Naganori Yamaguchi (assisted by OpenAI
Codex)", followed by Worker 114's dated modification record. Worker 114 took
this proof directly from the pinned original and the published statement module.
There are no project coauthors. The unchanged inherited
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are already
in the Library and are not modified.

The pinned source is registered as `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`),
with attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
The whole source file has SHA-256
`29a3ec39fcabc17faa969f1c4c225a7cfd07555a00298e58daaa4b6fa6c7bb60`, recomputed by
Worker 114 on 15 November 2026 UTC. The
[port partition](../../../../../../../notes/reuse/nyll-public-port/m289-m312.md#m301)
lists this unit as `M301.004` in module M301 (no patch10 edit applies).

The development environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`). There the module
compiles with no errors or warnings, and the theorem depends only on `propext`,
`Classical.choice` and `Quot.sound`. Compilation is not acceptance:
publication under `lean.proof@1` also requires the Lake build, exact-target and
unchanged-statement checks, independent semantic review and integration.
