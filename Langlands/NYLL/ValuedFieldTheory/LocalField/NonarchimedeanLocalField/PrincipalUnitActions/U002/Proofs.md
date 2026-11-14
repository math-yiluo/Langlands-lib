# Valuation-ring equivalences map the maximal ideal to itself: exact proof

This module proves `Langlands.NYLL.LocalFieldTheory.integerRingEquiv_map_maximalIdeal`
with exactly the closed type
`Langlands.NYLL.LocalFieldTheory.integerRingEquiv_map_maximalIdealStatement.{u}`.
Its universe parameter is `u`. The published statement module
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitActions.MaximalIdealStatements`
is imported unchanged.

The proposition's complete internal telescope is

```lean
∀ (K : Type u) [Field K] [ValuativeRel K]
  (e : 𝒪[K] ≃+* 𝒪[K]),
  Ideal.map e.toRingHom (𝓂[K] : Ideal 𝒪[K]) = (𝓂[K] : Ideal 𝒪[K])
```

Here `𝒪[K]` is Mathlib's scoped notation for
`Valuation.integer (ValuativeRel.valuation K)` and `𝓂[K]` is
`IsLocalRing.maximalIdeal 𝒪[K]`, using Mathlib's local-ring instance on
`𝒪[K]`. The theorem says that the image ideal of the maximal ideal under
an arbitrary ring automorphism `e` of `𝒪[K]` is the maximal ideal itself.
No topology or local-field hypothesis is assumed.

## Implemented proof

After introducing `K`, its two structure instances and `e`:

1. The local fact `hmem : ∀ x : 𝒪[K], e x ∈ 𝓂[K] ↔ x ∈ 𝓂[K]` is the source proof of
   M135.001 for `e`: rewriting with `IsLocalRing.mem_maximalIdeal`, then
   `map_mem_nonunits_iff e` (whose `IsLocalHom e` hypothesis is Mathlib's
   instance `isLocalHom_equiv`), then `IsLocalRing.mem_maximalIdeal`
   backwards.
2. The remaining tactic block is the original source proof of M135.002,
   with each source call `integerRingEquiv_mem_maximalIdeal K e _` replaced
   by `hmem _`. By `ext y` and `constructor`:
   - if `y ∈ Ideal.map e.toRingHom 𝓂[K]`, then
     `Ideal.mem_map_iff_of_surjective` with `e.surjective` gives `x ∈ 𝓂[K]`
     with `e x = y`, and `(hmem x).2` gives `e x ∈ 𝓂[K]`;
   - if `y ∈ 𝓂[K]`, the same lemma reduces membership in the image to the
     witness `e.symm y`, mapped to `y` by `e.apply_symm_apply y`; `simpa`
     turns the hypothesis into `e (e.symm y) ∈ 𝓂[K]` and `(hmem (e.symm y)).1`
     gives `e.symm y ∈ 𝓂[K]`.

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
opening, lines 24–29 the statement and proof of M135.001, and the routed
range of M135.002 is lines 32–49 (the next unit, M135.003, starts at
line 50).

The source theorem `LocalFieldTheory.integerRingEquiv_map_maximalIdeal`
becomes the identically suffixed theorem in the `Langlands.NYLL` namespace.
This is the proof phase of M135.002 in
`notes/reuse/nyll-public-port/m121-m144.md`. The source proof uses the
M135.001 theorem `integerRingEquiv_mem_maximalIdeal`, whose proof is a
separate candidate of the same task and is not yet in the Library. As the
task permits, this proof does not import it and does not declare a second
copy: the one-line source proof of M135.001 is inlined as the local fact
`hmem` inside the proof. Apart from that replacement the source tactic block
is unchanged.

Worker 135 made these changes on 14 November 2026:

- Prefix the namespace with `Langlands.NYLL`.
- State the theorem with the published closed proposition as its entire type,
  preserving universe `.{u}` and the binder order and kinds, and introduce
  that telescope with `intro`.
- Inline the source proof of M135.001 as the local fact `hmem` and use it
  in place of the two source calls of that theorem.
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
