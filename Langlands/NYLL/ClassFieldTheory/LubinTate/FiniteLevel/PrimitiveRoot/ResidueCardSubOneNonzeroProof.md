# The residue cardinality minus one is nonzero (M341.008)

This module proves
`Langlands.NYLL.LubinTate.residueFieldNatCard_sub_one_cast_ne_zero`
with the fully applied imported type
`Langlands.NYLL.LubinTate.residueFieldNatCard_sub_one_cast_ne_zeroStatement F`.
The target is defined in
`Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveRoot.DerivativeCardinalityStatements`.
It says that
`((Nat.card F.residueField - 1 : ℕ) : K) ≠ 0`.
The subtraction occurs in the natural numbers before the cast.

The theorem retains independent universes `u v`, implicit
`{K : Type u} [Field K]` and explicit
`(F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u,v} K)`.
The supplied package contains a chosen complete discrete valuation and a finite
residue field. It supplies all finiteness needed by this proof. The theorem has
no additional hypothesis and takes no uniformizer.

## Implemented proof

Write `q = Nat.card F.residueField`. The proof first unfolds the imported
statement, then performs the following steps.

1. Install `Fintype.ofFinite F.residueField` locally. Rewrite
   `Nat.card_eq_fintype_card` and `Nat.cast_card_eq_zero` to show that the
   cast of `q` into the residue field is zero.
2. The residue field is a nontrivial finite field, so `Finite.one_lt_card`
   gives `1 < q`. Its weaker consequence `1 ≤ q` justifies `Nat.cast_sub`.
   Thus the cast of `q - 1` in the residue field is `0 - 1 = -1`, which
   is nonzero by `neg_ne_zero.mpr one_ne_zero`.
3. Suppose the cast of `q - 1` in `K` were zero. Use `Subtype.ext` to
   obtain the same equality in `F.valuationSubring`. Apply the ring
   homomorphism `F.residueMap`; its preservation of natural-number casts
   and zero gives a zero cast in the residue field, contradicting step 2.

`Mathlib.FieldTheory.Finite.Basic` supplies `Nat.cast_card_eq_zero`.
The published target import supplies the local-field package, its residue map
and the cardinality API. The proof adds no helper declarations or instances
outside its local proof. It uses no assumption about the characteristic of `K`.

## Source and modifications

This is a focused adaptation of Naganori Yamaguchi's NYLL
ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/PrimitiveRoot.lean`,
M341.008: the declaration and proposition are at lines 123–125 and its
proof is at lines 126–145. The source file SHA-256 is
`b9d4862f4873c982618ff0f591c73b251f7a6f6f3d4fc6e93134b6d4ecb732b4`.
The original section telescope is at lines 32–42.

The source is registered as
`external-lean-reuse-snapshots-2026-10-21`
(fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
with attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
The readable pinned source is in the project's literature collection under
`External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

Worker 233 made these modifications:

- Extracted only M341.008, preserving its theorem name and parameter
  telescope and qualifying its namespace with `Langlands.NYLL`.
- Replaced the written-out proposition by the fully applied published
  target and added its initial unfolding. The remaining proof body follows
  the source unchanged.
- Replaced the original four imports by the published target module and
  `Mathlib.FieldTheory.Finite.Basic`. Dropped the unused polynomial scope.
- Replaced the module documentation and added a modification notice.

The original 2026 copyright, Apache-2.0 release and author header are
preserved verbatim. The existing `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`)
are retained without modification. The target pair and all its imports are
also retained. Upstream used Lean 4.35.0-rc2; this proof is checked in the
project's Lean 4.34.0 / Mathlib
`5ed2965256430c3649e86755f9576b54eca72435` environment.
