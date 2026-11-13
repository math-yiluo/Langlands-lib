# NYLL M075.028: `n z = k` in `ℤ̂` with `k < n` forces `k = 0`

This module proves the published Library proposition
`Langlands.NYLL.ClassFormation.abstractReciprocity_zHat_nsmul_eq_natCast_forces_zeroStatement`
by the theorem
`Langlands.NYLL.ClassFormation.abstractReciprocity_zHat_nsmul_eq_natCast_forces_zero`.
The theorem's type is exactly that proposition applied to its source
parameters,
`abstractReciprocity_zHat_nsmul_eq_natCast_forces_zeroStatement n k hn hk z h`.
It has no universe parameters.

Its sole direct import is
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core.ZHat.Statements`.
That published Lean/Markdown pair and its complete imported chain remain
unchanged.

## Target and parameters

The theorem has, in this order, explicit natural numbers `n k : ℕ`,
explicit hypotheses `hn : 0 < n` and `hk : k < n`, an explicit profinite
integer `z : ZHat`, and the explicit hypothesis
`h : n • z = Int.castRingHom ZHat (k : ℤ)`. Here `ZHat` is the published
closure model of `ℤ̂ = lim ℤ/nℤ` (M008, `GaloisCohomology/ProfiniteIntegers/ProfiniteIntegerCore/Definitions`),
`n • z` is the natural-number multiple in its additive group, and
`Int.castRingHom ZHat (k : ℤ)` is the image of the integer `k` under the
canonical ring homomorphism `ℤ →+* ZHat`.

Unfolding the published proposition gives the conclusion `k = 0`: if the
image of `k` in `ℤ̂` is divisible by `n` and `0 ≤ k < n`, then `k = 0`.

## Implemented proof

The complete proof body is

```lean
  have hkmod : (k : ZMod n) = 0 := by
    have hkmodInt : ((k : ℤ) : ZMod n) = 0 := by
      calc
        ((k : ℤ) : ZMod n) = zHatReduction n hn
          (Int.castRingHom ZHat (k : ℤ)) := rfl
        _ =
          zHatReduction n hn (n • z) := congrArg (zHatReduction n hn) h.symm
        _ = n • zHatReduction n hn z := map_nsmul (zHatReduction n hn) n z
        _ = 0 := by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    simpa using hkmodInt
  exact Nat.eq_zero_of_dvd_of_lt
    ((ZMod.natCast_eq_zero_iff k n).1 hkmod) hk
```

The goal
`abstractReciprocity_zHat_nsmul_eq_natCast_forces_zeroStatement n k hn hk z h`
is the published `def` with body `k = 0`; the final `exact` closes it by
definitional unfolding. The argument reduces modulo `n` with the published
continuous additive homomorphism `zHatReduction n hn : ZHat → ZMod n`
(M008.018), which evaluates an element of the closure model at the modulus
`n`.

1. **Reduction of the integer `k`.** The first `calc` step,
   `((k : ℤ) : ZMod n) = zHatReduction n hn (Int.castRingHom ZHat (k : ℤ))`,
   holds by `rfl`: the integer cast into `ZHat` is the cast into the closure
   subring of `∀ i, ZMod i.modulus`, whose component at modulus `n` is the
   cast of `k` into `ZMod n`, and `zHatReduction n hn` reads off exactly that
   component.
2. **Using `h`.** Rewriting backwards along `h` gives
   `zHatReduction n hn (n • z)`.
3. **Additivity.** Mathlib's `map_nsmul` for the additive homomorphism
   `zHatReduction n hn` gives `n • zHatReduction n hn z`.
4. **Vanishing mod `n`.** Mathlib's `nsmul_eq_mul`, `ZMod.natCast_self`
   (`(n : ZMod n) = 0`) and `zero_mul` show this is `0`.
5. **From `ℤ` to `ℕ` casts.** `simpa` rewrites `((k : ℤ) : ZMod n)` to
   `(k : ZMod n)` (Mathlib's `Int.cast_natCast`), giving `hkmod`.
6. **Conclusion.** Mathlib's `ZMod.natCast_eq_zero_iff k n` turns `hkmod`
   into `n ∣ k`, and `Nat.eq_zero_of_dvd_of_lt` together with `hk : k < n`
   yields `k = 0`.

The hypothesis `hn` is used only to form `zHatReduction n hn`. No auxiliary
declaration, extra hypothesis, instance or `simp` registration is
introduced. The development check reports only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`.

### Adaptation: the integer-reduction step

In the source the first `calc` step is justified by
`(zHatReduction_int n hn (k : ℤ)).symm`, citing M009.007
`ClassFormation.zHatReduction_int`
(`Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean`, lines
110–116), the identity
`zHatReduction n hn ((Int.castRingHom ZHat) a) = (a : ZMod n)`. That lemma
is not yet in the Library. Its own source proof is `rfl` (line 116), and in
the port the same identity holds definitionally over the published `ZHat`
and `zHatReduction`, so the citation is replaced by `rfl` (the symmetric
form of a definitional equality is again `rfl`). All other steps are the
original text.

## Actual dependencies

- The published proposition
  `Langlands.NYLL.ClassFormation.abstractReciprocity_zHat_nsmul_eq_natCast_forces_zeroStatement`
  in `Core/ZHat/Statements` (unfolded only).
- The published `Langlands.NYLL.ClassFormation.ZHat`, its ring structure
  and `Langlands.NYLL.ClassFormation.zHatReduction` in
  `GaloisCohomology/ProfiniteIntegers/ProfiniteIntegerCore/Definitions`,
  reached through the unchanged import chain.
- Mathlib's `Int.castRingHom`, `map_nsmul`, `nsmul_eq_mul`,
  `ZMod.natCast_self`, `zero_mul`, `Int.cast_natCast` (via `simpa`),
  `ZMod.natCast_eq_zero_iff` and `Nat.eq_zero_of_dvd_of_lt`.

The unpublished M009.007 `zHatReduction_int` is not used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Core.lean:1157–1176`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Core.lean#L1157-L1176).
Lines 1157–1158 are the retained docstring, 1159–1163 the signature and
conclusion, and 1164–1176 the tactic proof retained above, with lines
1168–1169 the replaced `zHatReduction_int` step. The whole-file SHA-256 of
`Core.lean` is
`0fc1bd5c66d628b74e079fd54af4a9df7334343e38186983257da5ce6a8f06fb`, and
that of `ProfiniteInteger.lean` is
`b2fcb523b7bf0408b776c71df6d528d446d7d373634df6e5df43183d57fc5ae6`, both
recomputed by Worker 9 on 13 November 2026 UTC from the retained snapshot.

| Original in `ClassFormation` | Adapted in `Langlands.NYLL.ClassFormation` |
| --- | --- |
| Asserted type of `abstractReciprocity_zHat_nsmul_eq_natCast_forces_zero` (M075.028) | Published `abstractReciprocity_zHat_nsmul_eq_natCast_forces_zeroStatement` in `Core/ZHat/Statements` |
| Proof `abstractReciprocity_zHat_nsmul_eq_natCast_forces_zero` | This theorem of the same adapted name in `Core/ZHat/U028/Proofs` |
| `(zHatReduction_int n hn (k : ℤ)).symm` (M009.007) | `rfl` |
| `ZHat`, `zHatReduction` (M008) | Existing published definitions in `ProfiniteIntegerCore/Definitions` |

The adaptation prefixes the namespace with `Langlands.NYLL`, replaces the
original imports by the sole published `Core/ZHat/Statements` import, states
the theorem's type as the published proposition applied to
`n k hn hk z h`, and makes the `rfl` replacement above. The
[public partition](../../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m075)
places this proof at M075.028 after M075.027.END; no patch10 edit applies
to M075.

The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including "Naganori Yamaguchi
(assisted by OpenAI Codex)", followed by Worker 9's dated modification
record. Worker 9 extracted this proof directly from the pinned original
and the published statement. No unpublished project draft was reused, and
there are no project coauthors.

The unchanged inherited [LICENSE](../../../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are retained, with
SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`
respectively.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`:
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Development compilation is separate from acceptance. Publication under
`lean.proof@1` requires the Lake build, kernel and exact-target checks,
unchanged statement and dependency checks, independent semantic review and
Integrator publication.

This proof covers only the elementary step M075.028. M009.007 itself, the
valuation identities of M075.029 onward and any host class-formation or
reciprocity theorem are separate work.
