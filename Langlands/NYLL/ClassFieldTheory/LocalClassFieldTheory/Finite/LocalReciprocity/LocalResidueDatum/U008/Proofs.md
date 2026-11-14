# The chosen separable valuation extends the local valuation: proof and instance

This module proves the published closed target
`Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationHasExtensionStatement`
([target](Statements.md), NYLL source unit M249.008) by the theorem

```lean
theorem localSeparableValuationHasExtension :
    localSeparableValuationHasExtensionStatement
```

in namespace `Langlands.NYLL.LocalClassFieldTheory`, the adapted source name.
The target is a reducible `abbrev`, so the module then registers the theorem
as a global instance, as the source does:

```lean
attribute [instance] localSeparableValuationHasExtension
```

Its type is the target. Neither has a level parameter. The theorem says that
for a nonarchimedean local field `K : Type`, the valuation of the chosen
valuation ring `localSeparableValuationSubring K` of `SeparableClosure K`
extends the canonical valuation `(localCompleteDVF K).valuation` of `K`
(Mathlib's `Valuation.HasExtension`). After the instance attribute, any
module importing this one finds that `Valuation.HasExtension` instance by
instance search.

## Proof

The proof follows the source body (lines 110–113). That body applies the
published theorem
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.hasExtension_valuation_of_valuationSubring_pullback`
(M110.004,
[proof](../../../../../../ValuedFieldTheory/Valuation/DiscreteValuationField/ChevalleyExtension/U004/Proofs.md)):
for a valuation `vK` of `K` and a valuation subring `B` of an extension field
`L`, if `algebraMap K L x ∈ B ↔ x ∈ vK.valuationSubring` for every `x : K`,
then `vK.HasExtension B.valuation`. Here `vK = (localCompleteDVF K).valuation`,
`B = localSeparableValuationSubring K` and `L = SeparableClosure K`.

The source passes its theorem `localSeparableValuationSubring_pullback K`
(M249.007) as the pullback hypothesis. Its statement is published
([target](../U007/Statements.md)), but its proof is a separate unit. So this
module proves the hypothesis in place, as a `fun x => by ...` block that is
the source proof of M249.007 (lines 99–104). The block uses the private
source lemma M249.004 (`localAbsoluteValuationSubring_pullback`, lines 66–76),
which is inlined as a `have`. The module therefore depends on no unpublished
proof.

Before the theorem, the module installs the two published local instances of
the source with

```lean
attribute [local instance] Langlands.NYLL.PortInternal.M249.d001
  Langlands.NYLL.PortInternal.M249.d002
```

They are the algebra `SeparableClosure K → AlgebraicClosure K` given by the
inclusion (M249.001) and the scalar tower
`K → SeparableClosure K → AlgebraicClosure K` (M249.002), both from the
[definitions module](../U006/Definitions.md). They are local to this module
and do not occur in the theorem's type.

After `intro` of `K` and its four instance binders, the proof is an `exact`
of the M110.004 theorem applied to the canonical valuation, the chosen ring
and the following proof of the pullback condition at `x : K`:

1. **The chosen ring of the algebraic closure pulls back to `K`** (the source
   lemma M249.004). The `have habsolute` states that for every `y : K`,
   `algebraMap K (AlgebraicClosure K) y ∈ d003 K` if and only if `y` lies in
   the valuation subring of `(localCompleteDVF K).valuation`. Here `d003 K`
   (M249.003) is by definition `Classical.choose` of the published Chevalley
   theorem `exists_extension_valuationSubring` (M110.003), applied to
   `L := AlgebraicClosure K` and the canonical valuation of `K`.
   `Classical.choose_spec` of the same term gives three properties of the
   chosen ring. The third, `hpullback`, is exactly the claim at `y`.
2. **Reduction to the algebraic closure.** By definition,
   `localSeparableValuationSubring K` is the preimage of `d003 K` under the
   algebra map `SeparableClosure K → AlgebraicClosure K` of `d001`. So
   `change` restates the left side of the goal, up to definitional equality, as
   `algebraMap (SeparableClosure K) (AlgebraicClosure K)
   (algebraMap K (SeparableClosure K) x) ∈ d003 K`.
3. **The tower.** `rw [← IsScalarTower.algebraMap_apply K (SeparableClosure K)
   (AlgebraicClosure K)]`, using the scalar tower `d002`, turns the composite
   into `algebraMap K (AlgebraicClosure K) x`.
4. `habsolute x` closes the goal.

## Checks

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) compiled the module
with no errors or warnings. Inspection of the theorem reported kind `theorem`,
no level parameters, and only the axioms `propext`, `Classical.choice` and
`Quot.sound`. A private client module that imports this one proved
`(localCompleteDVF K).valuation.HasExtension (localSeparableValuationSubring K).valuation`
by `inferInstance`, which confirms the instance registration. Worker 401
repeated both checks on 14 November 2026 in the same environment, with the
same results.

## Imports

- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U008.Statements`
  is the published target. Through it come the definitions module (`d001`,
  `d002`, `d003`, `localSeparableValuationSubring`), `localCompleteDVF` and
  the Chevalley theorem `exists_extension_valuationSubring`.
- `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.U004.Proofs`
  supplies `hasExtension_valuation_of_valuationSubring_pullback`.

The published target and definitions are used by name, and none of them is
modified.

## Source correspondence and changes

The original declaration is the instance
`LocalClassFieldTheory.localSeparableValuationHasExtension` at lines 106–113
of Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean#L106-L113)
at commit `fbd320cd8b1b06487c58227e92eb135794267709` (file SHA-256
`be13bf4f92820faee2f89e127b56f6bbf23a8f5a4fe93fd2e5e58745ca7d4396`). Its type
is the published target. Its body cites the source theorem M249.007 (lines
94–104), whose proof uses the private lemma M249.004 (lines 66–76).

Worker 3 made these changes on 13 November 2026:

- the instance becomes the theorem `localSeparableValuationHasExtension` of
  the closed target, followed by `attribute [instance]` for it. The proof
  begins with `intro` of the section variables;
- the body's scoped `open … in` names the published namespace
  `Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation` instead of
  the source's `ValuationTheory.DiscreteValuationField.Valuation`;
- the citation of `localSeparableValuationSubring_pullback K` (M249.007) is
  replaced by its source proof, with the source names replaced by the
  published ones: `localAbsoluteValuationSubring` becomes
  `Langlands.NYLL.PortInternal.M249.d003`. The proof of M249.004 (lines 72–76)
  is copied into the `have`, with the published names
  `exists_extension_valuationSubring` and `localCompleteDVF` spelled out in
  full. The partition's internal name for M249.004,
  `Langlands.NYLL.PortInternal.M249.d004`, is not declared;
- the source's file-wide local instances are replaced by
  `attribute [local instance]` of the published `d001` and `d002`;
- the doc comment is the source's. Of the source module's `open` lines
  (lines 33–43), only `LocalFieldTheory` is kept, as
  `open Langlands.NYLL.LocalFieldTheory`; the others are omitted, and the
  source imports are replaced by the two published modules above.

The module is Worker 3's shared task draft (revision 1). Worker 401 submits
it with Worker 3 as coauthor; the Lean file is unchanged, and the Markdown
edits only clarify the wording and record the repeated checks.

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
