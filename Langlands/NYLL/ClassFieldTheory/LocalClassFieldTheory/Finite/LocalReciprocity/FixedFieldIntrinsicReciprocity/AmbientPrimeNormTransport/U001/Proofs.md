# Valuation-one units under valuation-compatible ring equivalences: proof

This module proves the published closed proposition
`Langlands.NYLL.LocalClassFieldTheory.exists_valuationOne_unit_of_ringEquivStatement`
(NYLL source unit M283.001) by the theorem
`Langlands.NYLL.LocalClassFieldTheory.exists_valuationOne_unit_of_ringEquiv`.
It also adds three helper lemmas about the published normalized valuation
map. Its only direct import is the statement module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeNormTransport.U001.Statements`.
The statement pair and everything it imports are unchanged.

## Exact target

The theorem's type is exactly `exists_valuationOne_unit_of_ringEquivStatement`.
Unfolded, it says:

```lean
∀ (L M : Type)
  [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]
  [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M]
  (phi : L ≃+* M),
  (∀ x : L,
    x ∈ (ValuativeRel.valuation L).valuationSubring ↔
      phi x ∈ (ValuativeRel.valuation M).valuationSubring) →
  ∃ p : Lˣ,
    valuationMap L (Additive.ofMul p) = 1 ∧
      valuationMap M (Additive.ofMul (Units.mapEquiv phi.toMulEquiv p)) = 1
```

where `valuationMap` is the published
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap`.
For a nonarchimedean local field `K`, `valuationMap K : Additive Kˣ →+ ℤ`
sends a unit `x` to the integer that corresponds to `v_K(x)` under
Mathlib's order isomorphism
`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K : ValueGroupWithZero K ≃*o ℤᵐ⁰`.

## Helper lemmas

All three are in the namespace `Langlands.NYLL.LocalClassFieldTheory` and are
stated for an arbitrary nonarchimedean local field `K : Type`.

1. `coe_valuationUnitsMulHom_eq K x`: for `x : Kˣ`, the element
   `valuationUnitsMulHom K x : Multiplicative ℤ`, viewed in `ℤᵐ⁰`, equals
   `valueGroupWithZeroIsoInt K (valuation K x)`. The proof unfolds the
   published `valuationUnitsMulHom` (a composite of `Units.map` and
   `WithZero.unitsWithZeroEquiv`) and closes the goal with `simp`.
2. `valuationMap_nonpos_iff K x`: `valuationMap K (ofMul x) ≤ 0` holds
   exactly when `x` lies in the valuation subring of `valuation K`. The
   value `valuationMap K (ofMul x)` is by definition the `toAdd` of
   `valuationUnitsMulHom K x`. So `≤ 0` means `≤ 1` in `Multiplicative ℤ`, and
   by `WithZero.coe_le_coe` and lemma 1 this becomes
   `valueGroupWithZeroIsoInt K (valuation K x) ≤ valueGroupWithZeroIsoInt K 1`.
   An order isomorphism reflects `≤` (`map_le_map_iff`), so this is
   `valuation K x ≤ 1`, which is membership in the valuation subring
   (`Valuation.mem_valuationSubring_iff`).
3. `exists_valuationMap_eq_one K`: some `x : Kˣ` has
   `valuationMap K (ofMul x) = 1`. Mathlib's
   `ValuativeRel.valuation_surjective` gives `y : K` whose valuation is the
   preimage of `ofAdd 1` under the isomorphism. This value is nonzero, so
   `y ≠ 0`, and `x = Units.mk0 y _`. Lemma 1 with `apply_symm_apply` and
   `WithZero.coe_inj` gives `valuationUnitsMulHom K x = ofAdd 1`, whose
   `toAdd` is `1`.

## Proof of the theorem

After introducing the binders, the proof works with two additive
homomorphisms `Additive Lˣ →+ ℤ`:

- `F = valuationMap L`, and
- `G = valuationMap M ∘ (Units.mapEquiv phi.toMulEquiv)`, written as the
  composite of `valuationMap M` with the additive version of the unit
  equivalence. So `G (ofMul x)` is by definition
  `valuationMap M (ofMul (Units.mapEquiv phi.toMulEquiv x))`.

The steps are:

1. **Same nonpositive part.** For every `a`, `F a ≤ 0 ↔ G a ≤ 0`. Write
   `a = ofMul x`. By lemma 2 on both sides and `Units.coe_mapEquiv`, this is
   the hypothesis: `x` lies in the valuation subring of `L` exactly when
   `phi x` lies in that of `M`.
2. **Kernel inclusion.** If `F a = 0`, then `F a ≤ 0` and `F (-a) = -F a ≤ 0`.
   By step 1, `G a ≤ 0` and `-G a = G (-a) ≤ 0`, so `G a = 0` (`omega`).
3. **Witnesses.** Lemma 3 gives `p : Lˣ` with `F (ofMul p) = 1` and
   `q' : Mˣ` with `valuationMap M (ofMul q') = 1`. Let `q` be the preimage
   of `q'` under the unit equivalence; then `G (ofMul q) = 1`.
4. **Positivity.** `G (ofMul p) > 0`: otherwise `G (ofMul p) ≤ 0`, so by
   step 1 `F (ofMul p) ≤ 0`, contradicting `F (ofMul p) = 1`.
5. **Conclusion.** Let `b = F (ofMul q)` and
   `a = ofMul q - b • ofMul p`. Then `F a = b - b * 1 = 0`, so `G a = 0`
   by step 2. Expanding with `map_sub` and `map_zsmul` gives
   `1 = b * G (ofMul p)`. Since `G (ofMul p) ≥ 0`,
   `Int.eq_one_of_mul_eq_one_left` gives `G (ofMul p) = 1`.

The witness is `p`, with `F (ofMul p) = 1` and `G (ofMul p) = 1`, which is
exactly the conclusion.

The proof uses no uniformizer and no fact about valuation rings beyond the
stated membership hypothesis.

## Comparison with the original proof

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/AmbientPrimeNormTransport.lean`
(SHA-256
`b430f3810416cb42cc7c61df63be3691b219a5fe39c0bc7c0c2a74292298bfa0`),
lines 28–90: docstring 28–29, signature 30–45, proof 46–90. The original
proof builds the ring equivalence `𝒪[L] ≃+* 𝒪[M]` induced by `phi`, takes a
chosen uniformizer of `𝒪[L]`, transports its irreducibility, and takes `p`
to be the inverse of the uniformizer. It then uses the NYLL lemma
`v_integerRingIrreducibleFieldUnit_inv` (the inverse of an irreducible
element of the valuation ring has normalized valuation one) for `L` and for
`M`. Those NYLL lemmas are not in the Library. The proof here is new: it uses
only Mathlib and the published definition of `valuationMap`, and its witness
`p` is any unit of normalized valuation one.

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Attribution

The Lean header keeps the original 2026 Naganori Yamaguchi copyright,
authorship line and Apache-2.0 notice, because the theorem name and statement
come from the original. The proof and the three helper lemmas were written by
Worker 56 and shared as Task 5988 draft revision 1. Worker 216 adopted that
proof unchanged, checked the source correspondence and revised this proof
documentation on 13 November 2026. Both contributions are recorded in the Lean
modification header. The retained
[LICENSE](../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) are unchanged.

No instance or simp attribute is installed.
