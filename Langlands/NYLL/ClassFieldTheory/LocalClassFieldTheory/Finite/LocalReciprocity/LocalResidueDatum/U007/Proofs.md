# Pullback of the chosen separable valuation ring: proof

This module proves the published closed target
`Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring_pullbackStatement`
([target](Statements.md), NYLL source unit M249.007) by the theorem

```lean
theorem localSeparableValuationSubring_pullback :
    localSeparableValuationSubring_pullbackStatement
```

in namespace `Langlands.NYLL.LocalClassFieldTheory`, the adapted source name.
Its type is the target; neither has a level parameter. The theorem says: for a
nonarchimedean local field `K : Type` and `x : K`, the image of `x` in
`SeparableClosure K` lies in the chosen valuation ring
`localSeparableValuationSubring K` exactly when `x` lies in the valuation ring
of the canonical valuation of `K`.

## Proof

The proof follows the source proof (lines 99–104), with the source's private
lemma M249.004 (`localAbsoluteValuationSubring_pullback`, lines 66–76) inlined
as a `have`.

Before the theorem, the module installs the two published local instances of
the source with

```lean
attribute [local instance] Langlands.NYLL.PortInternal.M249.d001
  Langlands.NYLL.PortInternal.M249.d002
```

that is, the algebra `SeparableClosure K → AlgebraicClosure K` given by the
inclusion (M249.001) and the scalar tower
`K → SeparableClosure K → AlgebraicClosure K` (M249.002), both from the
[definitions module](../U006/Definitions.md). The attribute is local to this
module; nothing is exported except the theorem.

After `intro` of `K`, its four instance binders and `x`:

1. **The chosen ring of the algebraic closure pulls back to `K`** (the source
   lemma M249.004). The `have` states that for every `y : K`,
   `algebraMap K (AlgebraicClosure K) y ∈ d003 K` if and only if `y` lies in
   the valuation subring of `(localCompleteDVF K).valuation`. Here
   `d003 K` (M249.003) is by definition `Classical.choose` of the published
   Chevalley theorem `exists_extension_valuationSubring` (M110.003), applied
   to `L := AlgebraicClosure K` and the canonical valuation of `K`.
   `Classical.choose_spec` of the same term gives the three properties of the
   chosen ring; the third one, `hpullback`, is exactly the claim at `y`.
2. **Reduction to the algebraic closure.** By definition,
   `localSeparableValuationSubring K` is the preimage of `d003 K` under the
   algebra map `SeparableClosure K → AlgebraicClosure K` of `d001`. So the
   `change` tactic rewrites the left side of the goal to
   `algebraMap (SeparableClosure K) (AlgebraicClosure K)
   (algebraMap K (SeparableClosure K) x) ∈ d003 K`.
3. **The tower.** `rw [← IsScalarTower.algebraMap_apply K (SeparableClosure K)
   (AlgebraicClosure K)]`, using the scalar tower `d002`, turns the composite
   into `algebraMap K (AlgebraicClosure K) x`.
4. Step 1 at `y := x` closes the goal.

## Checks

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) compiled the module
with no errors or warnings, both for Worker 3 and, on 14 November 2026 over
Library commit `c40a01345b2f4172fa41e07ff31644b40e695003`, for Worker 399.
Inspection of the theorem reported kind `theorem`, no level parameters, and
only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Imports

The only import is the published target module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U007.Statements`.
Through it come the definitions module (`d001`, `d002`, `d003`,
`localSeparableValuationSubring`), `localCompleteDVF` and the Chevalley theorem
`exists_extension_valuationSubring`. The published target and definitions are
used by name; none of them is modified.

## Source correspondence and changes

The original theorem is
`LocalClassFieldTheory.localSeparableValuationSubring_pullback` at lines
94–104 of Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean#L94-L104)
at commit `fbd320cd8b1b06487c58227e92eb135794267709` (file SHA-256
`be13bf4f92820faee2f89e127b56f6bbf23a8f5a4fe93fd2e5e58745ca7d4396`). Its
statement is the published target. The proof also uses the source's private
lemma `localAbsoluteValuationSubring_pullback` (M249.004, lines 66–76).

Worker 3 made these changes on 13 November 2026:

- the theorem proves the closed target, so the proof begins with `intro` of
  the section variables and of `x`;
- the source proof (lines 99–104) is kept, with the source names replaced by
  the published ones: `localAbsoluteValuationSubring` becomes
  `Langlands.NYLL.PortInternal.M249.d003`, and the final step uses the inlined
  `have` instead of the source lemma M249.004;
- the proof of M249.004 (lines 72–76) is copied into that `have`, with the
  published names `exists_extension_valuationSubring` and `localCompleteDVF`
  spelled out in full; the partition's internal name for M249.004,
  `Langlands.NYLL.PortInternal.M249.d004`, is not declared;
- the source's file-wide local instances are replaced by
  `attribute [local instance]` of the published `d001` and `d002`.

The Lean file and this Markdown are Worker 3's shared draft for this task
(draft revision 1). Worker 399 submits it with the Lean file unchanged; the
only edits are to this Markdown's Checks section and this paragraph.

## Provenance and license

The readable original is in registration
`external-lean-reuse-snapshots-2026-10-21` (content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`), with
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`). The Lean
file keeps the original copyright and author header verbatim and records the
modifications. The Apache-2.0
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are unchanged in the
Library.
