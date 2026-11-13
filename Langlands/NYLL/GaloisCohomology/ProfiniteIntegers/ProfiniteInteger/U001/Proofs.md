# NYLL M009.001: uniqueness of natural generator powers

This module proves the already published proposition
`Langlands.NYLL.ClassFormation.proCIntegerOne_pow_nat_injectiveStatement`.
The theorem
`Langlands.NYLL.ClassFormation.proCIntegerOne_pow_nat_injective` has exactly
that named proposition as its type and has no parameters. It asserts injectivity
of
`fun n : ℕ => (Multiplicative.ofAdd (1 : ZHat)) ^ n`
for the published closure model `Langlands.NYLL.ClassFormation.ZHat`.

The source is Naganori Yamaguchi's
`Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
SHA-256 `b2fcb523b7bf0408b776c71df6d528d446d7d373634df6e5df43183d57fc5ae6`.
This proof adapts unit M009.001, source lines 28–49, with signature at
lines 31–33. The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

The implemented proof retains the source argument. Given equal powers at
natural exponents `a` and `b`, applying `Multiplicative.toAdd` gives
`a • (1 : ZHat) = b • (1 : ZHat)`. Set `m := a + b + 1`.
Then `m` is positive and both exponents are strictly below `m`.
Apply the actual continuous additive reduction `zHatReduction m hm`.
Its value at one is definitionally one, proved by `rfl` from the published
closure-coordinate model. Using `map_nsmul` therefore gives equality of the
natural casts of `a` and `b` in `ZMod m`. Apply `ZMod.val` and
`ZMod.val_natCast_of_lt` at the two strict bounds to conclude `a = b`.

The local names `m`, `hm`, `ha`, `hb`, `habAdd`, `habAdd'`, `habRed`,
`hredOne` and `hval` correspond directly to the same local steps in the
source proof. No separately declared helper theorem is introduced or assumed.

The only direct import is
`Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Statements`.
It supplies the named target, the published natural-multiplication data module,
the published closure-model data module and their Mathlib dependencies. This
proof uses the existing `ZHat` operations and `zHatReduction`, together with
Mathlib's additive/multiplicative conversion, additive-homomorphism and
`ZMod.val` facts and the `simp`, `omega`, `rw`, `change` and `simpa` tactics.
The separate M008 theorem proofs and other M009 theorem proofs are not needed.

Worker 236 extracts the source theorem, prefixes its namespace with
`Langlands.NYLL`, replaces the source's expanded injectivity type by the
definitionally equal published Statement name, and replaces the original
imports by the target module. The proof body is unchanged. The published
statement pair and its imports are unchanged.

The original copyright, Apache-2.0 license and author header are retained.
See `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`,
and `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
This contribution proves only the stated exponent-uniqueness proposition.
