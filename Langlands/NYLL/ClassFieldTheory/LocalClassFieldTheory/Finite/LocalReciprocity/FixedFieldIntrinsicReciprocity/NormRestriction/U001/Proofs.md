# Restriction of embedded Galois actions on ambient quotient representatives: proof

This module proves the published closed proposition
`Langlands.NYLL.LocalClassFieldTheory.AmbientEmbeddedFixedFieldPresentation.quotientRestrictionStatement`
(NYLL source unit M288.001) by the theorem
`Langlands.NYLL.LocalClassFieldTheory.AmbientEmbeddedFixedFieldPresentation.quotientRestriction`.
Its only import is the statement module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.NormRestriction.U001.Statements`,
which brings in the published M086.019 definition
`normResidueNaturalityAbelianizedRestriction`. The statement pair and
everything it imports are unchanged.

## Exact target

The theorem has no universe parameters and its type is exactly
`AmbientEmbeddedFixedFieldPresentation.quotientRestrictionStatement`. Its
complete telescope is displayed in the statement's Markdown (`Statements.md`
beside this file). For finite abelian Galois extensions `L/K` and
`L'/K'` of nonarchimedean local fields, with `K'/K` finite separable, ambient
fixed-field presentations `lower` of `L/K` along `jLower` and `upper` of
`L'/K'` along `jUpper` inside `SeparableClosure K`, ambient inclusions `hH'H`
and `hJ'J`, seven instance hypotheses, and `restrictActual : Gal(L'/K') →*
Gal(L/K)`, if

- `hbase`: `∀ x : L, jUpper (algebraMap L L' x) = jLower x`, and
- `hcompat`: `∀ τ x, jLower (restrictActual τ x) = jUpper (τ (algebraMap L L' x))`,

then for every `z` in the abelianization of the ambient quotient of `upper`,

```lean
restrictActual
    ((Abelianization.equivOfComm (H := Gal(L' / K'))).symm
      ((upper.extension.extensionQuotientMulEquiv.symm.trans
        upper.quotientEquiv).abelianizationCongr z)) =
  (Abelianization.equivOfComm (H := Gal(L / K))).symm
    ((lower.extension.extensionQuotientMulEquiv.symm.trans
      lower.quotientEquiv).abelianizationCongr
      (normResidueNaturalityAbelianizedRestriction
        lower.base.field upper.base.field
        lower.extension.field upper.extension.field
        lower.extension.below upper.extension.below
        hH'H hJ'J z))
```

## Proof

After introducing the binders (the twenty-four instance binders of the
field data and the seven instance hypotheses are introduced anonymously and
remain local instances), write `qLower` and `qUpper` for the two
identifications `extensionQuotientMulEquiv.symm.trans quotientEquiv` of the
ambient quotients with `Gal(L/K)` and `Gal(L'/K')`.

1. By `QuotientGroup.mk_surjective` twice (first for the abelianization,
   which is a quotient group, then for the ambient quotient), `z` is the class
   `Abelianization.of (QuotientGroup.mk sigma)` of some `sigma` in the base
   subgroup of `upper`.
2. A local identity `hof` states that the ambient abelianized restriction of
   this class is
   `Abelianization.of (QuotientGroup.mk (Subgroup.inclusion hH'H sigma))`.
   It is proved by Mathlib's `Abelianization.map_of`: the published
   definition `normResidueNaturalityAbelianizedRestriction` is
   `Abelianization.map (finiteReciprocityNaturalityRestriction …)`, and the
   published `finiteReciprocityNaturalityRestriction` sends `QuotientGroup.mk
   sigma` to `QuotientGroup.mk (Subgroup.inclusion hH'H sigma)` by definition.
   `rw [hof]` performs the replacement.
   Two rewrites with Mathlib's `abelianizationCongr_of` move `qUpper` and
   `qLower` inside `Abelianization.of`, and `change` (using that
   `Abelianization.equivOfComm` inverts `Abelianization.of`) reduces the goal
   to `restrictActual (qUpper [sigma]) = qLower [Subgroup.inclusion hH'H sigma]`
   in `Gal(L/K)`.
3. Two auxiliary identities rewrite `qUpper [sigma]` as
   `upper.quotientEquiv (upper.extension.extensionQuotientMk sigma)` and
   similarly for `qLower`. Their inner step
   `extensionQuotientMulEquiv.symm [sigma] = extensionQuotientMk sigma` holds
   by `rfl`: the published `FiniteGaloisSubextension.extensionQuotientMulEquiv`
   is `MulEquiv.refl _` and `extensionQuotientMk` is `QuotientGroup.mk'`.
4. Two elements of `Gal(L/K)` are equal when they agree on every `x : L`
   (`AlgEquiv.ext`), and `jLower` is injective, so it suffices to compare
   their images under `jLower`. The `calc` chain uses `hcompat`, the first
   auxiliary identity, the structure field `upper.quotientEquiv_mk_apply`
   (the quotient equivalence acts through `jUpper` as `sigma` acts on
   `SeparableClosure K`), `hbase` (so `jUpper (algebraMap L L' x) = jLower x`),
   the definitional equality of `sigma` and `Subgroup.inclusion hH'H sigma`
   as automorphisms, `lower.quotientEquiv_mk_apply` and the second auxiliary
   identity.

The proof has the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Original correspondence

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/NormRestriction.lean`
(SHA-256
`cd6f508f2695bb024ae28041740f78edbd1cb03492d287248ddaba7bb115e9a3`),
theorem `LocalClassFieldTheory.AmbientEmbeddedFixedFieldPresentation.quotientRestriction`:
docstring lines 26–27, signature lines 28–98, proof lines 99–186.

Adaptation changes:

- The theorem gets the `Langlands.NYLL` namespace prefix and proves the
  published closed proposition instead of carrying the binders in its
  signature. The proof therefore starts with `intro`.
- The source rewrites with the theorem
  `normResidueNaturalityAbelianizedRestriction_of_mk` (source unit M086.020).
  The adaptation proves the same
  instance as the local identity `hof` by `Abelianization.map_of` (step 2) and
  rewrites with that. The source proof of M086.020 is the same argument
  (`Abelianization.lift_apply_of` followed by `rfl`).
- In the two auxiliary identities the source proves the inner step by
  `extensionQuotientMulEquiv.symm_apply_eq.mpr (extensionQuotientMk_apply …).symm`,
  using the source theorem `FiniteGaloisSubextension.extensionQuotientMk_apply`
  (source unit M040.012). The adaptation
  proves the same identity by `rfl` instead, which holds because of the
  published definitions named in step 3.
- Everything else (the `let`s, the two `obtain`s, the `change`s, the
  `AlgEquiv.ext` reduction and the six-step `calc`) is the original proof.
- The original imports are replaced by the single import above. All other
  declarations of the source module are omitted. The source docstring is
  kept. The `open` lines are the statement module's.

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Attribution

The Lean header keeps the original 2026 Naganori Yamaguchi copyright,
authorship line and Apache-2.0 notice, followed by a dated modification
record by Worker 56 and an adoption record by Worker 699. Worker 699 reused
Worker 56's shared draft revision 1, checked the pinned original lines 1–186
and the current Library defining equations, and kept the proof body unchanged.
Worker 56 is recorded as a coauthor of this contribution. The retained
[LICENSE](../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) are unchanged.

No instance or simp attribute is installed. The development check reports
no errors or warnings.
