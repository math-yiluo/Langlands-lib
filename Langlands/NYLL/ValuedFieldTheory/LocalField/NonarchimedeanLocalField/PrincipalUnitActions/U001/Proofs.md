# Valuation-ring equivalences preserve the maximal ideal: exact proof

This module proves `Langlands.NYLL.LocalFieldTheory.integerRingEquiv_mem_maximalIdeal`
with exactly the closed type
`Langlands.NYLL.LocalFieldTheory.integerRingEquiv_mem_maximalIdealStatement.{u}`.
Its universe parameter is `u`. The published statement module
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitActions.MaximalIdealStatements`
is imported unchanged.

The proposition's complete internal telescope is

```lean
∀ (K : Type u) [Field K] [ValuativeRel K]
  (e : 𝒪[K] ≃+* 𝒪[K]) (x : 𝒪[K]),
  e x ∈ (𝓂[K] : Ideal 𝒪[K]) ↔ x ∈ (𝓂[K] : Ideal 𝒪[K])
```

Here `𝒪[K]` is Mathlib's scoped notation for
`Valuation.integer (ValuativeRel.valuation K)` and `𝓂[K]` is
`IsLocalRing.maximalIdeal 𝒪[K]`, using Mathlib's local-ring instance on
`𝒪[K]`. The theorem says that an arbitrary ring automorphism `e` of
`𝒪[K]` maps an element into the maximal ideal exactly when the element is
already there. No topology or local-field hypothesis is assumed.

## Implemented proof

After introducing `K`, its two structure instances, `e` and `x`, the proof is
the original source rewrite chain:

1. `IsLocalRing.mem_maximalIdeal` rewrites `e x ∈ 𝓂[K]` as
   `e x ∈ nonunits 𝒪[K]`.
2. `map_mem_nonunits_iff e` rewrites this as `x ∈ nonunits 𝒪[K]`. Its
   hypothesis `IsLocalHom e` is Mathlib's instance `isLocalHom_equiv` for
   multiplicative equivalences: an equivalence reflects units.
3. Rewriting backwards with `IsLocalRing.mem_maximalIdeal` turns the left
   side into `x ∈ 𝓂[K]`, and `rw` closes the resulting reflexive `Iff`.

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
opening, and the routed range of M135.001 is lines 24–31 (statement and
proof at lines 24–29; the next unit, M135.002, starts at line 32).

The source theorem `LocalFieldTheory.integerRingEquiv_mem_maximalIdeal`
becomes the identically suffixed theorem in the `Langlands.NYLL` namespace.
This is the proof phase of M135.001 in
`notes/reuse/nyll-public-port/m121-m144.md`. The rewrite chain is copied
unchanged; only the closed target's telescope is introduced first.

Worker 135 made these changes on 14 November 2026:

- Prefix the namespace with `Langlands.NYLL`.
- State the theorem with the published closed proposition as its entire type,
  preserving universe `.{u}` and the binder order and kinds, and introduce
  that telescope with `intro`.
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
  instance, `IsLocalRing.mem_maximalIdeal`, `map_mem_nonunits_iff` and
  `isLocalHom_equiv`.

The original import, NYLL `NonarchimedeanLocalField.PrincipalUnitQuotients`,
is unnecessary for this proof. No NYLL declaration is used.

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
