# Membership in maximal-ideal powers under valuation-ring equivalences: exact proof

This module proves `Langlands.NYLL.LocalFieldTheory.integerRingEquiv_mem_maximalIdeal_pow`
with exactly the closed type
`Langlands.NYLL.LocalFieldTheory.integerRingEquiv_mem_maximalIdeal_powStatement.{u}`.
Its universe parameter is `u`. The published statement module
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitActions.MaximalIdealStatements`
is imported unchanged.

The proposition's complete internal telescope is

```lean
∀ (K : Type u) [Field K] [ValuativeRel K]
  (e : 𝒪[K] ≃+* 𝒪[K]) (n : Nat) (x : 𝒪[K]),
  e x ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) ↔ x ∈ (𝓂[K] ^ n : Ideal 𝒪[K])
```

Here `𝒪[K]` is Mathlib's scoped notation for
`Valuation.integer (ValuativeRel.valuation K)` and `𝓂[K]` is
`IsLocalRing.maximalIdeal 𝒪[K]`, using Mathlib's local-ring instance on
`𝒪[K]`. The theorem says that an arbitrary ring automorphism `e` of
`𝒪[K]` maps an element into `𝓂[K] ^ n` exactly when the element is already
there. No topology or local-field hypothesis is assumed.

## Implemented proof

After introducing `K`, its two structure instances, `e`, `n` and `x`:

1. The local fact
   `hpow : ∀ f : 𝒪[K] ≃+* 𝒪[K], Ideal.map f.toRingHom (𝓂[K] ^ n) = 𝓂[K] ^ n`
   is the source proof of M135.003, preceded by those of M135.001 and
   M135.002, for an arbitrary ring automorphism `f`:
   - the local fact `hmem : ∀ x : 𝒪[K], f x ∈ 𝓂[K] ↔ x ∈ 𝓂[K]` is the
     source proof of M135.001 for `f`: rewriting with
     `IsLocalRing.mem_maximalIdeal`, then `map_mem_nonunits_iff f` (whose
     `IsLocalHom f` hypothesis is Mathlib's instance `isLocalHom_equiv`),
     then `IsLocalRing.mem_maximalIdeal` backwards;
   - the local fact `hmap : Ideal.map f.toRingHom 𝓂[K] = 𝓂[K]` is the
     source proof of M135.002 for `f`, using
     `Ideal.mem_map_iff_of_surjective`, `f.surjective`,
     `f.apply_symm_apply` and `hmem`;
   - `rw [Ideal.map_pow, hmap]` concludes.
   It is quantified over `f` because the source applies M135.003 both to `e`
   and to `e.symm`.
2. The remaining tactic block is the original source proof of M135.004,
   with the source rewrites by `integerRingEquiv_map_maximalIdeal_pow K e.symm n`
   and `integerRingEquiv_map_maximalIdeal_pow K e n` replaced by `hpow e.symm`
   and `hpow e`. By `constructor`:
   - if `e x ∈ 𝓂[K] ^ n`, then `Ideal.mem_map_of_mem e.symm.toRingHom` gives
     `e.symm (e x) ∈ Ideal.map e.symm.toRingHom (𝓂[K] ^ n)`; rewriting with
     `hpow e.symm` and simplifying `e.symm (e x)` to `x` (`simpa`) gives
     `x ∈ 𝓂[K] ^ n`;
   - if `x ∈ 𝓂[K] ^ n`, then `Ideal.mem_map_of_mem e.toRingHom` gives
     `e x ∈ Ideal.map e.toRingHom (𝓂[K] ^ n)`, and rewriting with `hpow e`
     gives `e x ∈ 𝓂[K] ^ n`.

## Source and correspondence

The original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitActions.lean`,
SHA-256 `42c0bc7ef0a080024990e1d4f323703c5e8965cb3fce29074318d4ab2bf82194`.
It is available in registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement
is `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Lines 1–80 were read. Lines 15–21 supply the namespace, universe and scoped
opening, lines 24–29, 32–47 and 50–55 the statements and proofs of M135.001,
M135.002 and M135.003, and the routed range of M135.004 is lines 58–75 (the
next unit, M135.005, starts at line 76).

The source theorem `LocalFieldTheory.integerRingEquiv_mem_maximalIdeal_pow`
becomes the identically suffixed theorem in the `Langlands.NYLL` namespace.
This is the proof phase of M135.004 in
`notes/reuse/nyll-public-port/m121-m144.md`. The source proof rewrites with
the M135.003 theorem `integerRingEquiv_map_maximalIdeal_pow`, which rests on
M135.001 and M135.002. Their proofs are separate candidates of the same task
and are not yet in the Library. As the task permits, this proof does not
import them and does not declare second copies: their source proofs are
inlined as the single local fact `hpow`, quantified over the ring
automorphism. Apart from these replacements the source proofs are unchanged.

Worker 135 made these changes on 14 November 2026:

- Prefix the namespace with `Langlands.NYLL`.
- State the theorem with the published closed proposition as its entire type,
  preserving universe `.{u}` and the binder order and kinds, and introduce
  that telescope with `intro`.
- Inline the source proofs of M135.001–003, for an arbitrary ring
  automorphism `f`, as the local fact `hpow`, and rewrite with `hpow e.symm`
  and `hpow e` in place of the two source rewrites by
  `integerRingEquiv_map_maximalIdeal_pow`.
- Omit all other declarations of the original file, its
  `noncomputable section` and its `universe` declaration.
- Replace the original import by the single import below.
- Retain the original copyright, license and author header and add the
  modification comment and this paired explanation.

## Actual imports

- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitActions.MaximalIdealStatements`
  supplies the exact published target and, through its Mathlib imports
  `Mathlib.Topology.Algebra.Valued.ValuativeRel` and
  `Mathlib.RingTheory.Ideal.Operations`, the notations, the local-ring
  instance and the Mathlib lemmas named above.

The original import, NYLL `NonarchimedeanLocalField.PrincipalUnitQuotients`,
is unnecessary for this proof. No NYLL proof is imported.

## Development check

In environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), the module compiled
with no errors or warnings. Declaration inspection reports a theorem with
level parameters `[u]` and only `propext`, `Classical.choice` and
`Quot.sound`. This development check is separate from candidate
exact-target validation and independent semantic review.

## Attribution

The retained original header credits Naganori Yamaguchi (assisted by OpenAI
Codex) and releases the source under Apache-2.0. The unchanged upstream
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are already published.
Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
No other worker's unpublished draft was reused.
