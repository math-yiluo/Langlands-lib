# The real rank-zero equal pair in normalized-growth form

This module proves the base case of the real normalized-growth induction: the
`GL₁ × GL₁` equal-rank pair. It is the real counterpart of the published complex
`ComplexJacquet.complexLocalEqualRankZeroGrowth`.

## Statement

`RealJacquet.RealLocalEqualRankZeroGrowthStatement` has these inputs:

- two real block lists `ds`, `es` of real rank `0 + 1`;
- a real unit `a` and real quotient measure data `D` for `GL₁(ℝ)`;
- `W` in `realUniformWhittakerModel 0 ds a` and `W'` in `realUniformWhittakerModel 0 es (-a)`;
- a Schwartz function `Φ` on `ℝ¹`.

The conclusion is `HasRealPairNormalizedGrowth` for the equal-rank integral
`realEqualIntegral D W W' Φ` and the dual integral `realEqualDualIntegral (-a) D W W' Φ`, with:

- dual lists `ds.map dualBlock` and `es.map dualBlock`;
- epsilon parameter `-a` and scale `sqrt |a|`;
- sign `det(ds, -1) ^ 0`.

These are the parameters that `RealLocalUniformPositiveEqualContinuationStatement` uses at
positive rank. At rank zero the sign is `1`. By
`HasRealPairNormalizedGrowth.equalContinuation`, the conclusion contains the corresponding
`EqualContinuation` package.

## Proof

1. A list of real rank one is a single character block
   (`RealRankZero.eq_singleton_of_realRank_eq_one`), so `ds = [character c]` and
   `es = [character c']`. The dual lists are `[character c.inverse]` and
   `[character c'.inverse]`.
2. The uniform model lies in the Library's real Whittaker model
   (`RealUniformWhittaker.model_le_model`). At rank one, every element of that model is a
   scalar multiple of the character composed with the determinant
   (`RealRankZero.exists_eq_of_mem_realWhittakerModel`). Hence `W = C · χ_c ∘ det` and
   `W' = C' · χ_{c'} ∘ det`.
3. The dual functions are `C · χ_{c⁻¹} ∘ det` and `C' · χ_{c'⁻¹} ∘ det`. The proof uses
   `dualFunction_apply`, the determinant of the inverse transpose, and the inverse of a unit
   value (private lemma `dual_rankZero_scalar`).
4. The published rank-one local functional equation `RealRankZero.realEqual_rankZero` is applied
   with the proved real Tate theory `RealTate.realArchimedeanTateStatement`, the parameter
   `-a`, and the dual characters `c.inverse`, `c'.inverse`. Their parities agree with those of
   `c`, `c'` and their exponents are negated. It gives meromorphic continuations and the
   codiscrete functional equation. Its epsilon factor is taken at the scale `sqrt |-a|`, which
   equals `sqrt |a|` (private lemma `realPairEpsilon_scale_congr`). The sign `x ^ 0` is `1`.
   This produces the `ContinuationPackage` for the target factors.
5. `RealRankZero.realRankZeroStripGrowth` gives an entire normalization with exponential strip
   growth for the ordinary integral. It applies a second time to the dual characters, the dual
   functions and a Schwartz function `Ψ` equal to the Fourier transform of `Φ` at parameter `-a`
   (`RealFourierSchwartz.exists_schwartz_eq`). That gives the same for the dual integral. Each
   normalization equals the integral divided by the reciprocal pair `L`-factor on a right
   half-plane. On a smaller half-plane, where the reciprocal factors are nonzero
   (`realLFactor_ne_zero`), multiplying back gives the agreement required by
   `HasRealPairNormalizedGrowth`.
6. The converse bridge `hasRealPairNormalizedGrowth_of_continuationPackage` combines the package,
   the two entire normalizations, their strip growth and the half-plane agreement into the
   normalized pair. The everywhere functional equation comes from the codiscrete one by the
   identity theorem and continuity.

## Provenance

This is the base case of the internal normalized-growth induction for the real place. It
follows the published complex `ComplexLocalEqualRankZeroGrowth`. Mathematically it is the
`GL₁ × GL₁` case of Jacquet, *Archimedean Rankin–Selberg integrals* (2009), Theorem 2.1
(ii)–(iii), which is Tate's local theory at the real place. The growth bound is exponential in
`|Im s|` on vertical strips, weaker than Jacquet's boundedness.
