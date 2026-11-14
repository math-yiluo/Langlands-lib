# Residue action of the field arithmetic Frobenius: proof

This module proves the published closed target of NYLL source unit M264.010,
`Langlands.NYLL.LocalFieldTheory.galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius_applyStatement`
(in [the target module](ResidueActionStatement.md)). It exports one theorem,

```lean
theorem galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius_apply :
    galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius_applyStatement.{u}
```

in namespace `Langlands.NYLL.LocalFieldTheory`, the adapted source name. Its type
is exactly the target at its universe `u`: for a finite Galois unramified
extension `L/K` of nonarchimedean local fields (with the integral-closure and
finiteness hypotheses of the target) and every `x : 𝓀[L]`, the residue action
of the field arithmetic Frobenius sends `x` to `x ^ Nat.card 𝓀[K]`.

## The proof

After introducing `K`, `L`, the instance arguments and `x`, the proof has two
steps.

1. **The residue action of Frobenius is residue Frobenius.** Write
   `e := galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure K L`
   (M161.036) and `r := residueExtensionArithmeticFrobeniusOfValuationExtension K L`
   (M264.001). By definition (M264.007),
   `arithmeticFrobeniusOfUnramifiedValuation K L` is `e.symm r`. The forward
   map of `e` is `MulEquiv.ofBijective` of the residue homomorphism
   `galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L`, whose underlying
   function is `galoisGroupResidueAlgEquivOfIsIntegralClosure K L`, both by
   definition. So the term `e.apply_symm_apply r : e (e.symm r) = r` (Mathlib's
   `MulEquiv.apply_symm_apply`) has, up to definitional unfolding, the type
   `galoisGroupResidueAlgEquivOfIsIntegralClosure K L (arithmeticFrobeniusOfUnramifiedValuation K L) = r`.
   Lean accepts it with that stated type, and `rw` with it turns the goal into
   `r x = x ^ Nat.card 𝓀[K]`.
2. **Residue Frobenius is the `q`-power map.** With the local `Fintype`
   structure `Fintype.ofFinite 𝓀[K]` (the residue field is finite by
   Mathlib's instance for `IsNonarchimedeanLocalField`), `r` is by definition
   Mathlib's `FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[K] 𝓀[L]`; `change`
   states this. Mathlib's `simp` lemma `coe_frobeniusAlgEquivOfAlgebraic`
   evaluates it to `x ^ Fintype.card 𝓀[K]`, and `Nat.card_eq_fintype_card`
   rewrites the right side, which closes the goal.

The source proves the theorem by rewriting with its simp lemma M264.009
(itself proved from M264.008 and M161.037) and then applying M264.002. This
proof inlines those four lemmas: step 1 is M264.008 together with M161.037 and
M264.009, and step 2 is the source proof of M264.002. None of them is needed
as a separate unit.

## Checks

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) compiled this module
and the target module with no errors or warnings. Inspection of the theorem
reported kind `theorem`, level parameters `[u]`, and only the axioms
`propext`, `Classical.choice` and `Quot.sound`. Worker 398 repeated this check
unchanged over Library commit `c40a01345b2f4172fa41e07ff31644b40e695003`, with
the same result (0 errors, 0 warnings, the same three axioms).

## Imports

The only import is the published target module
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnramifiedFrobenius.ResidueActionStatement`.
Through it the proof uses the published definitions above and Mathlib's finite
field Frobenius, `MulEquiv` and `Nat.card`.

## Source correspondence and changes

The original theorem is M264.010,
`LocalFieldTheory.galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius_apply`,
lines 175–190 of Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/UnramifiedFrobenius.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/UnramifiedFrobenius.lean#L175-L190)
at commit `fbd320cd8b1b06487c58227e92eb135794267709` (file SHA-256
`7839a2b17c7afc0b94c113a3b528b252dd05954e7452d282ff173d615b923104`).

Worker 3 made these changes on 13 November 2026:

- added the `Langlands.NYLL` namespace prefix to the theorem name;
- stated the theorem as a proof of the published closed target, so its
  parameters are introduced by `intro` instead of being written as
  declaration parameters;
- replaced the source proof (lines 189–190) by the two-step proof above;
- replaced the source imports by the published target module.

## Provenance and license

The readable original is in registration
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

The Lean file keeps the original copyright and author header verbatim
(copyright 2026 Naganori Yamaguchi; authors Naganori Yamaguchi, assisted by
OpenAI Codex) and records the modifications. The Apache-2.0
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are unchanged in the Library,
with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
