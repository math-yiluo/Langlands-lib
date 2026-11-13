# NYLL M008.022: transition compatibility for profinite-integer reductions

This module proves the published proposition
`Langlands.NYLL.ClassFormation.zHatReduction_transitionStatement` with theorem
`Langlands.NYLL.ClassFormation.zHatReduction_transition`. The theorem keeps
implicit `{m n : ℕ}` and explicit `(hm : 0 < m) (hn : 0 < n) (hmn : m ∣ n)
(x : ZHat)`, in that order. Its type is exactly the named target applied to
these parameters. Thus reduction modulo `n`, followed by
`ZMod.castHom hmn (ZMod m)`, equals reduction modulo `m` for every actual
closure-model point `x : ZHat`. No coherence premise is imposed on `x`.

## Source correspondence and attribution

The original is Naganori Yamaguchi's
`ClassFormation.zHatReduction_transition`, M008.022, in
`Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteIntegerCore.lean`,
lines 151–167 (signature 152–155), at commit
`fbd320cd8b1b06487c58227e92eb135794267709`. The source file SHA-256 is
`a6cdc6d3cfca209257868daa4e1aa09ca4f83d08927114958d2737b93b309ae5`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

The original copyright, author and Apache-2.0 header are retained in Lean.
The retained license is `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`;
the notice is `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

## Implemented proof and imports

The sole direct import is
`Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.Statements`.
It supplies the target, the actual `ZHat : Type 0` closure model, its instances,
`zHatReduction`, and the published internal support; its transitive
`TopologicalGeneration.Definitions` import is present because the statement
module also contains a generation target. No theorem about generation is used.

On the ambient product `PortInternal.M008.d004`, let `f` evaluate the
`n`-coordinate and then apply `ZMod.castHom`, and let `g` evaluate the
`m`-coordinate. The positive-modulus indices are `d003 n hn` and `d003 m hm`.
An element of the diagonal integer subring `d006` is the image under `d005`
of some integer `a`. Mathlib's `map_intCast` proves `f = g` at this image.
Both functions are continuous: coordinate evaluation is `continuous_apply`,
and the cast homomorphism is continuous by `continuous_of_discreteTopology`.
Mathlib's `Set.EqOn.closure` extends equality to the closure of the integer
subring. The membership proof `x.property` places the underlying ambient
point of `x` in that closure, so the resulting equality is definitionally
the asserted transition target.

Worker 192 extracted this single source proof, prefixed its namespace by
`Langlands.NYLL`, replaced the displayed equality theorem type by the exact
published proposition applied to the unchanged parameters, and replaced the
source-private support names `ZHatAmbient`, `zHatIndex`, and
`zHatIntegerSubring` by their published names `d004`, `d003`, and `d006`
under `Langlands.NYLL.PortInternal.M008`. The original file's imports are
replaced by the one published statement import. The proof route and mathematical
scope are unchanged. The target and all its imported files are unchanged;
no new definition, axiom, instance or hypothesis is introduced.
