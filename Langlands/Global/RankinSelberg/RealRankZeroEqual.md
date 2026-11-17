# The equal-rank real-place functional equation for `GL₁ × GL₁`

Helper module for the rank-one (`r = 0`) case of
`Langlands.Global.RankinSelbergGlobal.RealEqualFunctionalEquationStatement`. Authored by
Worker 823. Every declaration is proved. The main theorem `realEqual_rankZero_global`
assumes the Library proposition `Langlands.LocalFactor.RealArchimedeanTateStatement` as a
hypothesis `hTate`; nothing else beyond the stated hypotheses is assumed and no axioms are
added.

All declarations are in the namespace
`Langlands.Global.RankinSelbergGlobal.RealRankZero`. The module imports
`RealRankZeroLocal` (the local computation `realEqual_rankZero`) and
`RealRankZeroParameter` (Schur scalars, contragredient parameters and Whittaker
restrictions of cuspidal realizations of `GL₁`). The measurable structures on `ℝˣ`,
`GL₁(ℝ)`, `N₁(ℝ)` and `N₁(ℝ) \ GL₁(ℝ)` from `RealRankZeroHaar` are local instances; they
are the ones used by the Library's `RealQuotientMeasureData 0`.

## Declarations

- `eq_singleton_of_realRank_eq_one`: a list `d` of Library real blocks with
  `realRank d = 1` is `[character c]` for some `c : RealCharacterData`. A character block
  has rank `1` and an induced block has rank `2`.

- `realEqual_rankZero_global`: assume `hTate : RealArchimedeanTateStatement`. Let `F` be
  a number field with compact adele quotient, `χ` any additive character of the adeles
  (`AddChar (Adeles F) ℂ`), `T, Td, T', Td'` cuspidal operator realizations of `GL₁`
  (Library rank index `0`) with `Td` contragredient to `T` and `Td'` contragredient to
  `T'`, `v` a real place, `a ∈ ℝˣ`, and lists of real blocks `d, d', dd, dd'` that are
  real-place parameters at `v` of `T, T', Td, Td'`. Let `D : RealQuotientMeasureData 0`,
  `W, W' : GL₁(ℝ) → ℂ` with `IsRealPlaceWhittaker F T χ v W` and
  `IsRealPlaceWhittaker F T' χ⁻¹ v W'`, and `Φ` a Schwartz function on `ℝ¹`.
  Then the conclusion of `RealEqualFunctionalEquationStatement` at `r = 0` holds,
  including the factor `realMinusOneScalar T' v ^ 0`: there are `σ ∈ ℝ` and
  `M, Md : ℂ → ℂ` such that

  1. the integrand of `Ψ(s; W, W', Φ)` is `D.measure`-integrable for `Re s > σ`;
  2. the integrand of `Ψ(s; W̃, W̃', Φ̂)` (with `Φ̂ = realFourierTransform a Φ`) is
     `D.measure`-integrable for `Re s > σ`;
  3. `s ↦ realEqualIntegral D W W' Φ s` is holomorphic on `Re s > σ`;
  4. `s ↦ realEqualDualIntegral a D W W' Φ s` is holomorphic on `Re s > σ`;
  5. `M` is meromorphic on `ℂ`;
  6. `Md` is meromorphic on `ℂ`;
  7. `M` agrees with the first integral on `Re s > σ`;
  8. `Md` agrees with the dual integral on `Re s > σ`;
  9. for `s` outside a discrete subset of `ℂ` (the filter `codiscrete ℂ`),
     `L(s, d × d')⁻¹ · Md(1 - s) = ω'_v(-1)^0 · ε(s, d × d', ψ_a) · L(1 - s, dd × dd')⁻¹ · M(s)`,
     where `L` is the denominator of `realPairLFactor`, `ε` is `realPairEpsilon` normalized
     by `a` and `√|a|`, and `ω'_v(-1) = realMinusOneScalar T' v`.

  Compared with `RealEqualFunctionalEquationStatement` at `r = 0`, the theorem does not
  assume that `χ` is unitary, that it is trivial on `F`, or that `ψ_a` is the component of
  `χ` at `v` (`IsRealAdditiveComponent`). It does not use these hypotheses, so the statement
  at `r = 0` follows by specializing `χ` to `ψ.complex`.

### Proof

1. By `eq_singleton_of_realRank_eq_one` (the rank condition is the first component of
   `HasRealPlaceParameter`), `d = [character c]`, `d' = [character c']`,
   `dd = [character cd]` and `dd' = [character cd']`.
2. A cuspidal realization is irreducible, so `hasRealPlaceParameter_compact` and
   `hasRealPlaceParameter_lie` (module `RealRankZeroParameter`) show that `-1 ∈ O(1)` at
   `v` acts on `T` by `χ_c(-1)` and the Lie operator of `1 ∈ 𝔤𝔩₁(ℝ)` at `v` acts by
   `c.exponent`. Then `isRealPlaceWhittaker_rankZero` gives `W = C · χ_c ∘ det` for some
   `C ∈ ℂ`. In the same way `W' = C' · χ_{c'} ∘ det`. For `W'` the additive character is
   `χ⁻¹`; `isRealPlaceWhittaker_rankZero` holds for every additive character, because the
   `GL₁` Whittaker coefficient does not depend on it (`cuspWhittaker_rankZero`).
3. `contragredient_parity_rankOne` and `contragredient_exponent_rankOne` give
   `cd.parity = c.parity`, `cd'.parity = c'.parity`, `cd.exponent = -c.exponent` and
   `cd'.exponent = -c'.exponent`. Hence `cd.mul cd'` has the parity of `c.mul c'` and the
   negated exponent.
4. The local theorem `realEqual_rankZero hTate a c c' cd cd' hpar hexp D hC hC' Φ`
   (module `RealRankZeroLocal`) gives the nine conclusions with the factor
   `realMinusOneScalar T' v ^ 0` omitted. Since `x ^ 0 = 1`, the ninth conclusion is the
   same.

## Provenance

This is the case `n = n' = 1` of Jacquet, *Archimedean Rankin–Selberg integrals*
(2009), Theorem 2.1, at a real place. In this case the integrals are Tate's local zeta
integrals at the real place (Tate's thesis; Cassels–Fröhlich 1967, Chapter XV). The
reduction to `RealArchimedeanTateStatement` through Schur's lemma, the real-place
parameter and the contragredient pairing is internal to this project.
