# Galois automorphisms preserve an integral-closure valuation ring: exact proof

This module proves
`Langlands.NYLL.LocalFieldTheory.galoisGroup_mem_integerRing_of_isIntegralClosure`
with exactly the closed type
`Langlands.NYLL.LocalFieldTheory.galoisGroup_mem_integerRing_of_isIntegralClosureStatement.{u}`.
Its universe parameter is `u`. The published statement module
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing.PreservationStatement`
is imported unchanged.

The proposition's complete internal telescope is

```lean
∀ (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L]
  (σ : Gal(L/K)) (x : 𝒪[L]),
  σ (x : L) ∈ 𝒪[L]
```

Here `𝒪[K]` is Mathlib's scoped notation for
`Valuation.integer (ValuativeRel.valuation K)` and `Gal(L/K)` is the group
`L ≃ₐ[K] L` of `K`-algebra automorphisms of `L`. The hypothesis
`IsIntegralClosure 𝒪[L] 𝒪[K] L` says that `𝒪[L] → L` is injective and that
an element of `L` is integral over `𝒪[K]` exactly when it lies in the image
of `𝒪[L]`. The `HasExtension` hypothesis is part of the source telescope;
the proof does not refer to it explicitly. The theorem says that every
`K`-automorphism of `L` maps `𝒪[L]` into itself. No Galois, finiteness or
local-field hypothesis is assumed.

## Implemented proof

After introducing `K`, `L`, the seven structure instances, `σ` and `x`, the
proof is the original source tactic block:

1. `hx : IsIntegral 𝒪[K] (x : L)` is the backward direction of the
   integral-closure characterization `IsIntegralClosure.isIntegral_iff`
   (with `A := 𝒪[L]`, `R := 𝒪[K]`, `B := L`), applied to the witness
   `⟨x, rfl⟩`.
2. `hσ : IsIntegral 𝒪[K] (σ (x : L))` is Mathlib's `IsIntegral.map` applied
   to the `K`-algebra homomorphism `σ.toAlgHom` and `hx`. That lemma accepts
   an algebra homomorphism over the intermediate ring `K` because
   `𝒪[K] → K → L` is a scalar tower; integrality over `𝒪[K]` is preserved.
3. The forward direction of `IsIntegralClosure.isIntegral_iff` applied to
   `hσ` yields `y : 𝒪[L]` with `hy : (y : L) = σ (x : L)`.
4. `exact hy ▸ y.2` transports the membership proof `y.2 : (y : L) ∈ 𝒪[L]`
   along `hy` to the goal `σ (x : L) ∈ 𝒪[L]`.

## Source and correspondence

The original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/GaloisIntegerRing.lean`,
SHA-256 `5f84d148f49ea9a28bdcbd07b7d16e902ab47b6f47f37a88347848801bbb14b3`.
It is available in registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement
is `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Lines 1–55 were read. Lines 19–25 supply the namespace, universe and scoped
opening, and the routed range of M139.001 is lines 34–51 (docstring at lines
27–33; the next unit, M139.002, starts at line 52).

The source theorem
`LocalFieldTheory.galoisGroup_mem_integerRing_of_isIntegralClosure` becomes
the identically suffixed theorem in the `Langlands.NYLL` namespace. This is
the proof phase of M139.001 in `notes/reuse/nyll-public-port/m121-m144.md`.
The tactic block is copied unchanged; only the closed target's telescope is
introduced first. The docstring is shortened to its first sentence, without
the word "real" and the remark on the source's design history.

Worker 135 made these changes on 14 November 2026:

- Prefix the namespace with `Langlands.NYLL`.
- State the theorem with the published closed proposition as its entire type,
  preserving universe `.{u}` and the binder order and kinds, and introduce
  that telescope with `intro`.
- Shorten the docstring as described above.
- Omit all other declarations of the original file, its
  `noncomputable section` and its `universe` declaration.
- Replace the original imports by the single import below.
- Retain the original copyright, license and author header and add the
  modification comment and this paired explanation.

## Actual imports

- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing.PreservationStatement`
  supplies the exact published target and, through its import
  `GaloisIntegerRing.Definitions` and that module's Mathlib imports
  (`Mathlib.RingTheory.IntegralClosure.IntegralRestrict`,
  `Mathlib.RingTheory.Valuation.Extension`,
  `Mathlib.Topology.Algebra.Valued.ValuativeRel`), the notations, the
  subring algebra instances, `IsIntegralClosure.isIntegral_iff` and
  `IsIntegral.map`.

The original imports, `Mathlib.FieldTheory.Galois.IsGaloisGroup` and NYLL
`NonarchimedeanLocalField.Norm`, `PrincipalUnitActions`,
`ResidueExtension` and `Valuation`, are unnecessary for this proof. No NYLL
declaration is used; in particular, the published definition
`galoisGroupIntegerRingEquivOfIsIntegralClosure` in the imported definitions
module is not used.

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
