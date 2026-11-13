# Finite residue Frobenius exponent targets

Adapted by Worker 123 from Naganori Yamaguchi, ClassFieldTheory (NYLL), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteResidueFrobenius.lean`.
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M167.004 | `finiteResidueFrobeniusExponentHom_intCast` (64–77, `@[simp]`) | `finiteResidueFrobeniusExponentHom_intCastStatement` (`abbrev`) |
| M167.005 | `finiteResidueFrobeniusExponentHom_one` (79–85, `@[simp]`) | `finiteResidueFrobeniusExponentHom_oneStatement` (`abbrev`) |
| M167.006 | `finiteResidueFrobeniusExponentHom_surjective` (87–97) | `finiteResidueFrobeniusExponentHom_surjectiveStatement` |
| M167.007 | `finiteResidueFrobeniusExponentHom_injective` (99–109) | `finiteResidueFrobeniusExponentHom_injectiveStatement` |
| M167.012 | `finiteResidueFrobeniusFromZHat_apply` (150–157, `@[simp]`) | `finiteResidueFrobeniusFromZHat_applyStatement` (`abbrev`) |
| M167.013 | `finiteResidueFrobeniusFromZHat_one` (159–166, `@[simp]`) | `finiteResidueFrobeniusFromZHat_oneStatement` (`abbrev`) |
| M167.016 | `restrictNormalHom_finiteResidueFrobenius` (210–230) | `restrictNormalHom_finiteResidueFrobeniusStatement` |
| M167.017 | `restrictNormalHom_finiteResidueFrobeniusExponentHom` (232–270) | `restrictNormalHom_finiteResidueFrobeniusExponentHomStatement` |
| M167.018 | `restrictNormalHom_finiteResidueFrobeniusFromZHat` (272–289) | `restrictNormalHom_finiteResidueFrobeniusFromZHatStatement` |

Every unqualified original name above is in `LocalClassFieldTheory`; every
adapted name is in `Langlands.NYLL.LocalClassFieldTheory` unless fully qualified.
`ZHat`, `ZHatMul` and `zHatReduction` are the published
`Langlands.NYLL.ClassFormation` declarations.

## Content

Each target is the proposition of the source theorem, with the source's complete
parameter telescope. In the main section, `k : Type u` is a field with
`[Fintype k]` and `L : Type v` a finite `k`-algebra field (`[Finite L]`); write
`Frob = FiniteField.frobeniusAlgEquivOfAlgebraic k L` and `n = [L : k]`
(`Module.finrank k L`). Let `e = finiteResidueFrobeniusExponentHom k L` and
`φ = finiteResidueFrobeniusFromZHat k L`.

- M167.004, for `m : ℤ`: `e (ofAdd (m : ZMod n)) = Frob ^ m`.
- M167.005: `e (ofAdd (1 : ZMod n)) = Frob`.
- M167.006: `e` is surjective.
- M167.007: `e` is injective.
- M167.012, for `z : ZHatMul`: `φ z = e (ofAdd (zHatReduction n _ z.toAdd))`.
- M167.013: `φ (ofAdd (1 : ZHat)) = Frob`.

In the source section `Tower`, `{E : Type v} {F : Type w}` are finite fields
(`[Finite E] [Finite F]`) with `k`-algebra structures, an `E`-algebra structure
on `F`, `[IsScalarTower k E F]` and `[Normal k E]`; `AlgEquiv.restrictNormalHom E`
restricts `F ≃ₐ[k] F` to `E ≃ₐ[k] E`.

- M167.016: restriction sends `FiniteField.frobeniusAlgEquivOfAlgebraic k F` to
  `FiniteField.frobeniusAlgEquivOfAlgebraic k E`.
- M167.017, for `z : Multiplicative (ZMod [F : k])`: restriction of
  `finiteResidueFrobeniusExponentHom k F z` is
  `finiteResidueFrobeniusExponentHom k E` applied to the image of `z` under the
  reduction `ZMod.castHom` along `[E : k] ∣ [F : k]` (the divisibility witness
  is `[F : E]` with `Module.finrank_mul_finrank`, as in the source).
- M167.018, for `z : ZHatMul`: restriction of
  `finiteResidueFrobeniusFromZHat k F z` is `finiteResidueFrobeniusFromZHat k E z`.

## Modifications

- Namespace prefixed by `Langlands.NYLL`; each source theorem is replaced by a
  Prop-valued definition with the `Statement` suffix whose body is the source
  proposition verbatim. Source proofs are omitted; no theorem is proved here.
- The source `variable` blocks (lines 36–37 and 205–208), universes `u v w`,
  `open ClassFormation` and the `noncomputable section` are retained, so each
  target has the source theorem's binders in source order.
- Lean includes an instance-implicit section variable in a theorem whenever its
  dependencies are included, but in a definition only when it is used. The
  M167.016 proposition does not use the section hypothesis `[Finite E]`, which
  the source theorem nevertheless has. The M167.016 target therefore declares
  the `Tower` binders `{E : Type v} {F : Type w} [Field E] [Finite E] [Field F]
  [Finite F] [Algebra k E] [Algebra k F] [Algebra E F] [IsScalarTower k E F]
  [Normal k E]` itself, in source order, before the `Tower` `variable` command;
  its parameter list is then `k`, `[Field k]`, `[Fintype k]` followed by these,
  as for the source theorem. All other targets use every section binder of
  their source theorem (checked with `#check` in a private probe).
- The targets of the four source `@[simp]` theorems (M167.004, .005, .012, .013)
  are `abbrev`s, so that a later proof `theorem … : …Statement …` can carry the
  source `@[simp]` attribute. The attribute itself belongs to the proofs and is
  not on the targets.
- Imports: the sibling `Definitions` module only.

A private probe (not part of this unit) proves every target with the source
proof, assuming the unpublished `Langlands.NYLL.ClassFormation.zHatReduction_transitionStatement`
for M167.018, as the source does with `zHatReduction_transition`.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
