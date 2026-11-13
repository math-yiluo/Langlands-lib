# Natural multiplication of integer casts in the profinite integers

This module proves the theorem
`Langlands.NYLL.ClassFormation.zHatMulNat_int`. Its type is the already
published proposition `Langlands.NYLL.ClassFormation.zHatMulNat_intStatement`
applied to the theorem's two explicit parameters:

```lean
theorem zHatMulNat_int (n : ℕ) (a : ℤ) : zHatMulNat_intStatement n a
```

This is the proof phase of M009.009 in the
[NYLL partition](../../../../../../notes/reuse/nyll-public-port/m001-m024.md#m009).

## Target and parameters

The published statement in
`Langlands/NYLL/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger/Statements.lean`
unfolds to

```lean
zHatMulNat n ((Int.castRingHom ZHat) a) =
  (Int.castRingHom ZHat) ((n : ℤ) * a)
```

| Parameter | Kind | Meaning |
| --- | --- | --- |
| `n : ℕ` | explicit, first | The natural multiplier, arbitrary, including `0` |
| `a : ℤ` | explicit, second | The integer whose image in `ZHat` is multiplied |

The theorem keeps the source order `n` then `a` and adds no hypothesis; in
particular there is no positivity premise on `n`. The right side multiplies
in `ℤ` in the order `(n : ℤ) * a`, the cast of `n` on the left, and only then
maps to `ZHat` by Mathlib's `Int.castRingHom`.

`ZHat : Type 0` is the published NYLL closure model of
`ProfiniteIntegerCore/Definitions.lean`, with its published commutative ring
instance `Langlands.NYLL.PortInternal.M008.d009`. `zHatMulNat n` is the
published continuous additive map of `ProfiniteInteger/U002/Definitions.lean`,
whose function field is `fun x => n • x`, natural scalar multiplication for
the additive monoid of that ring. Both are imported unchanged by Lean name;
no other completion, topology, ring structure or multiplication map is used.

## Implemented proof

```lean
change n • (Int.castRingHom ZHat) a = (Int.castRingHom ZHat) ((n : ℤ) * a)
rw [map_mul, map_natCast, nsmul_eq_mul]
```

1. `change` unfolds the statement definition and the coercion of the
   bundled map `zHatMulNat n` to its function field, so the left side
   becomes `n • (Int.castRingHom ZHat) a`. This holds definitionally,
   the same fact as the source's `zHatMulNat_apply` (proved there by `rfl`);
   that theorem is not imported or used.
2. `map_mul` (Mathlib `Mathlib/Algebra/Group/Hom/Defs.lean`, line 326)
   rewrites the right side to
   `(Int.castRingHom ZHat) (n : ℤ) * (Int.castRingHom ZHat) a`.
3. `map_natCast` (`Mathlib/Data/Nat/Cast/Basic.lean`, line 138) for the ring
   homomorphism `Int.castRingHom ZHat` rewrites
   `(Int.castRingHom ZHat) (n : ℤ)` to the natural cast `(n : ZHat)`.
4. `nsmul_eq_mul` (`Mathlib/Algebra/Ring/Defs.lean`, line 187) rewrites the
   left side `n • (Int.castRingHom ZHat) a` to
   `(n : ZHat) * (Int.castRingHom ZHat) a`. Both sides now agree, and `rw`
   closes the goal by reflexivity.

So the proof is the ring identity `n • x = (n : ZHat) * x` combined with
multiplicativity of `Int.castRingHom` and its compatibility with natural
casts. It uses no extensionality principle for `ZHat`, no reduction map
`zHatReduction`, and no modular arithmetic.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean`, lines 125–136](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean#L125-L136):
the docstring at 125–128, the `@[simp]` attribute at 129, the theorem
signature at 130–132 and its proof at 133–136. The complete pinned file was
read and its SHA-256 verified as
`b2fcb523b7bf0408b776c71df6d528d446d7d373634df6e5df43183d57fc5ae6`.

The original proof applies `ZHat.ext` (M008.021), reduces to an identity
`n • (a : ZMod m) = (((n : ℤ) * a : ℤ) : ZMod m)` in every `ZMod m` with
`0 < m`, and closes it with `simp [nsmul_eq_mul]`. `ZHat.ext` is published
only as the statement `ZHat.extStatement`; its proof is routed to Task 5744.
This module therefore replaces the original proof by the direct argument
above, which the task explicitly allows. The theorem statement is unchanged.

| Original declaration | Adapted declaration in `Langlands.NYLL.ClassFormation` |
| --- | --- |
| `ClassFormation.zHatMulNat_int` (theorem) | `zHatMulNat_int`, proving the published target |
| Same theorem's statement | Existing `zHatMulNat_intStatement` |
| `ClassFormation.zHatMulNat` | Existing `zHatMulNat` |
| `ClassFormation.ZHat` | Existing `ZHat` |

Only the first row introduces a declaration here; no helper is added.
Modifications by Worker 105 on 13 November 2026: add the `Langlands.NYLL`
namespace prefix; replace the source imports with the sole import
`Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Statements`;
give the theorem the published proposition `zHatMulNat_intStatement n a` as
its type; replace the `ZHat.ext` proof by the direct proof; omit the `@[simp]`
attribute (the type is a statement definition, not a bare equation), the
noncomputable section and all other source declarations. The theorem name
and the docstring are kept.

The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`. Additional attribution
material is registered as `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Imports and checks

The sole direct import is the published Statements module. Through it the
proof sees the U002 Definitions module (for `zHatMulNat`), the
ProfiniteIntegerCore Definitions module (for `ZHat` and its instances) and
Mathlib. No imported Library module or paired Markdown is modified.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`
(Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`). A
development check built the module with no errors or warnings. It found a
theorem without universe parameters, using only the axioms `propext`,
`Classical.choice` and `Quot.sound`. This check does not establish
independent semantic acceptance or publication.

## Attribution and boundary

The original copyright and author header is preserved verbatim: copyright
2026 Naganori Yamaguchi, author “Naganori Yamaguchi (assisted by OpenAI
Codex)”, released under Apache-2.0. The Lean file carries the dated
modification record. Worker 105 wrote the replacement proof and this
companion; Worker 120's statement and the imported constructions are used
unchanged. The [LICENSE](../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are
included unchanged in `repository_paths`. No Mathlib code is copied.

This module proves only M009.009. It asserts no other M009 or M008 result,
no class-formation or reciprocity theorem, and no comparison with a host
model of the profinite integers.
