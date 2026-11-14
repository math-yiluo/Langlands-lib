# The Galois group of a finite unramified extension is cyclic: proof

This module proves the published closed target
`Langlands.NYLL.LocalFieldTheory.isCyclic_galoisGroup_of_unramifiedValuationStatement`
([target](CyclicStatement.md), NYLL source unit M264.016) by the theorem

```lean
theorem isCyclic_galoisGroup_of_unramifiedValuation :
    isCyclic_galoisGroup_of_unramifiedValuationStatement.{u}
```

in namespace `Langlands.NYLL.LocalFieldTheory`, the adapted source name. Its
type is the target at the same universe `u`. The theorem says: for a finite
Galois extension `L/K` of nonarchimedean local fields with a valuation
extension, whose integer ring `𝒪[L]` is the integral closure of `𝒪[K]` and
finite over it, and whose maximal ideal `𝓂[L]` has ramification index one,
the Galois group `Gal(L / K)` is cyclic.

## Proof

The proof does not follow the source. The source exhibits the field
arithmetic Frobenius as a generator (M264.006, M264.014, M264.015). Here the
cyclicity is transported from the residue extension, where Mathlib already
knows it.

After `intro` of `K`, `L` and all instance binders:

1. The published isomorphism
   `galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure K L :
   Gal(L / K) ≃* (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L])`
   (M161.036, [definition](../FiniteUnramified/ResidueEquivDefinitions.md))
   applies, since its parameters are exactly the binders of the target.
2. Mathlib's `MulEquiv.isCyclic` says that a group isomorphism `e : G ≃* G'`
   gives `IsCyclic G ↔ IsCyclic G'`. Its `mpr` direction reduces the goal to
   `IsCyclic (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L])`, that is, `IsCyclic Gal(𝓀[L] / 𝓀[K])`.
3. This is closed by `inferInstance`. Mathlib's instance in
   `Mathlib/FieldTheory/Finite/Basic.lean` gives `IsCyclic Gal(L' / K')` for
   any field extension `L'/K'` with `L'` finite; its generator is the
   Frobenius `frobeniusAlgEquivOfAlgebraic`. Instance search finds
   `Finite 𝓀[L]` from Mathlib's instance for the residue field of a
   nonarchimedean local field, and the residue algebra `𝓀[K] → 𝓀[L]` from
   the valuation extension.

No auxiliary declaration or instance is exported.

## Checks

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) compiled the module
with no errors or warnings. Inspection of the theorem reported kind `theorem`,
level parameters `[u]`, and only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Imports

- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnramifiedFrobenius.CyclicStatement`:
  the target and, through its imports, `MulEquiv.isCyclic`;
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified.ResidueEquivDefinitions`:
  the isomorphism M161.036 and, through its imports, Mathlib's cyclicity
  instance for Galois groups of finite fields.

The published target and definition are imported and used by name; neither is
modified.

## Source correspondence and changes

The original theorem is
`LocalFieldTheory.isCyclic_galoisGroup_of_unramifiedValuation` at lines
400–412 of Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/UnramifiedFrobenius.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/UnramifiedFrobenius.lean#L400-L412)
at commit `fbd320cd8b1b06487c58227e92eb135794267709` (file SHA-256
`7839a2b17c7afc0b94c113a3b528b252dd05954e7452d282ff173d615b923104`). Its
statement is the published target. Its proof, lines 410–412, rewrites with
`isCyclic_iff_exists_zpowers_eq_top` and supplies the arithmetic Frobenius with
the source lemma `arithmeticFrobeniusOfUnramifiedValuation_zpowers_eq_top`
(M264.015).

Worker 3 wrote the proof above on 13 November 2026. It replaces the source
proof and uses none of the source's proof code. The source's only reused
content is the theorem name and the statement, already in the published
target. The proof reuses the published Library declarations and Mathlib by
name.

## Provenance and license

The readable original is in registration
`external-lean-reuse-snapshots-2026-10-21` (content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`), with
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`). The Lean
file keeps the original copyright and author header verbatim and records the
modifications. The Apache-2.0
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are unchanged in the Library.
