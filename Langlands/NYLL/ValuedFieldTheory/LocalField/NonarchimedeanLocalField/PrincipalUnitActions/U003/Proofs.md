# Valuation-ring equivalences map maximal-ideal powers to themselves: exact proof

This module proves `Langlands.NYLL.LocalFieldTheory.integerRingEquiv_map_maximalIdeal_pow`
with exactly the closed type
`Langlands.NYLL.LocalFieldTheory.integerRingEquiv_map_maximalIdeal_powStatement.{u}`.
Its universe parameter is `u`. The published statement module
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitActions.MaximalIdealStatements`
is imported unchanged.

The proposition's complete internal telescope is

```lean
∀ (K : Type u) [Field K] [ValuativeRel K]
  (e : 𝒪[K] ≃+* 𝒪[K]) (n : Nat),
  Ideal.map e.toRingHom (𝓂[K] ^ n : Ideal 𝒪[K]) =
    (𝓂[K] ^ n : Ideal 𝒪[K])
```

Here `𝒪[K]` is Mathlib's scoped notation for
`Valuation.integer (ValuativeRel.valuation K)` and `𝓂[K]` is
`IsLocalRing.maximalIdeal 𝒪[K]`, using Mathlib's local-ring instance on
`𝒪[K]`. The theorem says that the image ideal of every power `𝓂[K] ^ n`
(with `𝓂[K] ^ 0 = ⊤`) under an arbitrary ring automorphism `e` of `𝒪[K]` is
the same power. No topology or local-field hypothesis is assumed.

## Implemented proof

After introducing `K`, its two structure instances, `e` and `n`:

1. The local fact `hmem : ∀ x : 𝒪[K], e x ∈ 𝓂[K] ↔ x ∈ 𝓂[K]` is the source proof of
   M135.001 for `e`: rewriting with `IsLocalRing.mem_maximalIdeal`, then
   `map_mem_nonunits_iff e` (whose `IsLocalHom e` hypothesis is Mathlib's
   instance `isLocalHom_equiv`), then `IsLocalRing.mem_maximalIdeal`
   backwards.
2. The local fact `hmap : Ideal.map e.toRingHom 𝓂[K] = 𝓂[K]` is the source proof of
   M135.002 for `e`: by `ext y` and `constructor`, the forward direction
   writes `y` as `e x` with `x ∈ 𝓂[K]` using
   `Ideal.mem_map_iff_of_surjective` and `e.surjective`, and concludes by
   `hmem x`; the backward direction exhibits `y` as the image of `e.symm y`
   (`e.apply_symm_apply y`), whose membership in `𝓂[K]` follows from
   `hmem (e.symm y)` after `simpa` identifies `e (e.symm y)` with `y`.
3. The final step is the original source proof of M135.003,
   `rw [Ideal.map_pow, hmap]`, with the source rewrite lemma
   `integerRingEquiv_map_maximalIdeal` replaced by `hmap`. Mathlib's
   `Ideal.map_pow` rewrites `Ideal.map e.toRingHom (𝓂[K] ^ n)` as
   `(Ideal.map e.toRingHom 𝓂[K]) ^ n`, `hmap` rewrites the base to `𝓂[K]`,
   and `rw` closes the reflexive equation.

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
opening, lines 24–29 and 32–47 the statements and proofs of M135.001 and
M135.002, and the routed range of M135.003 is lines 50–57 (the next unit,
M135.004, starts at line 58).

The source theorem `LocalFieldTheory.integerRingEquiv_map_maximalIdeal_pow`
becomes the identically suffixed theorem in the `Langlands.NYLL` namespace.
This is the proof phase of M135.003 in
`notes/reuse/nyll-public-port/m121-m144.md`. The source proof rewrites with
the M135.002 theorem `integerRingEquiv_map_maximalIdeal`, which in turn uses
M135.001. Their proofs are separate candidates of the same task and are not
yet in the Library. As the task permits, this proof does not import them and
does not declare second copies: their source proofs, specialized to `e`, are
inlined as the local facts `hmem` and `hmap` inside the proof. Apart from
these replacements the source proofs are unchanged.

Worker 135 made these changes on 14 November 2026:

- Prefix the namespace with `Langlands.NYLL`.
- State the theorem with the published closed proposition as its entire type,
  preserving universe `.{u}` and the binder order and kinds, and introduce
  that telescope with `intro`.
- Inline the source proofs of M135.001 and M135.002 for `e` as the local
  facts `hmem` and `hmap`, and rewrite with `hmap` in place of the source
  rewrite lemma `integerRingEquiv_map_maximalIdeal`.
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
