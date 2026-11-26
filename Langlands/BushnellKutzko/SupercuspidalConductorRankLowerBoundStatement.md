# Lower bound by rank for the conductor of a supercuspidal class

Module `Langlands.BushnellKutzko.SupercuspidalConductorRankLowerBoundStatement`, namespace
`Langlands.BushnellKutzko`. It imports `Langlands.Correspondence.HenniartNumericalStatement`,
which provides `Henniart.Numerical.conductor` and, through its imports,
`Correspondence.SupercuspidalAutomorphicClass`
(`Langlands/Correspondence/SupercuspidalRelations.lean`).

`SupercuspidalConductorRankLowerBoundStatement.{uK, uV} : Prop` is a proposition definition.
This file states it and does not prove it.

## Statement

For every `p : ℕ` with `[Fact p.Prime]`, every `K : PadicField.{uK} p`, every `k : ℕ` and every
`π : Correspondence.SupercuspidalAutomorphicClass.{uK, uV} K (k + 1).succPNat`,

```
((k + 2 : ℕ) : WithTop ℕ) ≤ Henniart.Numerical.conductor K π.
```

In words: an irreducible supercuspidal representation of `GL_N(K)` of rank `N ≥ 2` has
conductor at least `N`.

- **Rank.** `(k + 1).succPNat` is the positive natural number `k + 2`, so `π` is a class of
  irreducible supercuspidal representations of `GL_{k+2}(K)`. Every rank `N ≥ 2` occurs, as
  `N = k + 2` for `k = N - 2`. The implicit rank argument of `Henniart.Numerical.conductor` is
  `k + 1` here.
- **Classes.** `Correspondence.SupercuspidalAutomorphicClass K n` is the Library's space
  `PadicField.SupercuspidalClass` of isomorphism classes of irreducible admissible complex
  smooth representations of `GL_n(K)` whose Jacquet modules for all proper parabolic subgroups
  vanish (`GeneralLinear.IsSupercuspidal`). The field universe `uK` and the universe `uV` of
  the representation spaces are independent.
- **Conductor.** `Henniart.Numerical.conductor K π` is
  `GeneralLinear.SupercuspidalClass.firstFixedLevel π`: the least `a : ℕ` such that `π` has
  a nonzero vector fixed by the congruence subgroup of `GL_{k+2}(𝔬_K)` of matrices whose last
  row is congruent to `(0, …, 0, 1)` modulo `𝔭_K^a` (`Conductor.levelSubgroup`; at `a = 0`
  it is `GL_{k+2}(𝔬_K)`), and `⊤` if there is no such `a` (Jacquet–Piatetski-Shapiro–Shalika
  1981, §5). The value lies in `WithTop ℕ`. The statement does not assert finiteness.
  Finiteness is a separate theorem of the Library: `Conductor.supercuspidalPadicConductorExponent`
  gives, for a generic supercuspidal representation, a natural number `m` at which the
  newvector fixed space is a line and below which every fixed space is zero. The inequality
  holds trivially when the value is `⊤`.
- **Depth zero.** No hypothesis on the depth (normalized level) of `π` is made. Classes of
  depth zero, whose conductor is exactly `N`, are included.

The rank-one case is excluded on purpose: an unramified character of `GL_1(K) = K^×` is
supercuspidal and has conductor `0 < 1`.

## Mathematical origin

Let `N = k + 2`, and let `π` be an irreducible supercuspidal representation of
`G = GL_N(K)`. Bushnell (1987) works with the Godement–Jacquet local constant
`ε(π, s) = C(π) q^{-m(π)s}` (his (3.5)), relative to `ψ_A = ψ_F ∘ tr_A` on `A = M_N(F)`. Here
`ψ_F` is the Iwasawa–Tate character, whose conductor is the inverse different `𝔇_F^{-1}`, and
`𝔇_F = 𝔭^d` (his (3.6)).

1. **A nondegenerate constituent.** By Bushnell (1987), Theorem 3 and (5.1)(i), there is a
   principal order `𝔄` in `A`, of period `e = e(𝔄)`, such that the restriction of `π` to the
   normalizer `𝔊(𝔄)` of `𝔄` contains a nondegenerate irreducible representation `ρ`.
2. **Its conductor.** By (5.1)(ii), the conductor `𝔣(ρ)` of `ρ` is divisible by the radical
   `𝔓` of `𝔄`, so `𝔣(ρ) = 𝔓^{j+1}` with `j ≥ 0`. In the depth-zero case of the proof of
   Theorem 3, `𝔄` is a maximal order, `e = 1`, and `𝔣(ρ) = 𝔭𝔄`, that is `j = 0` (Remark
   (3.10)).
3. **The exponent.** By (5.1)(iv), formula (5.2), which is Bushnell–Fröhlich (1985),
   Theorem (3.3.8)(iv), in Bushnell's notation, and by the identity (3.8) in the proof of
   Theorem 3,
   `q^{m(π)} = (𝔄 : 𝔇_F 𝔭 𝔓^{-1} 𝔣(ρ))^{1/N}`.
   Since `𝔭𝔄 = 𝔓^e` and `(𝔄 : 𝔓^r) = q^{r N² / e}`, this gives
   `m(π) = N (1 + d + j / e)`, which is (3.7) with `f = j`.
4. **Normalizing the additive character.** Replacing `ψ` by `x ↦ ψ(a x)` multiplies
   `ε(π, s, ψ)` by `ω_π(a) |a|^{N(s - 1/2)}`. Taking `a` of order `-d`, so that the new
   character has conductor `𝔬_K`, removes `N d` from the exponent. The exponent for an
   additive character of conductor `𝔬_K` is therefore `N (1 + j / e) ≥ N`, since `j ≥ 0`
   and `e > 0`.
5. **Comparison with the first fixed level.** For `N = n + 1` with `n ≥ 1`, an additive
   character `ψ` with `Conductor.HasIntegerConductor ψ` (trivial on `𝔬_K` and on no larger
   fractional ideal) and a self-dual Haar measure, the Library theorem
   `GodementJacquet.Padic.exists_supercuspidalMatrixFunctionalEquationData` gives a
   Godement–Jacquet functional equation for `π` with both Euler polynomials `1`, a unit `c`
   and an exponent `a`. The Library theorem `exists_exponent_eq_firstFixedLevel` (module
   `Langlands.BushnellKutzko.ConductorBridge`) then gives `a = m` for a natural number `m`
   equal to `GeneralLinear.SupercuspidalClass.firstFixedLevel` of the class of `π`, which is
   `Henniart.Numerical.conductor K π`. With step 4, `m = N (1 + j / e) ≥ N = k + 2`.

The hypothesis `n ≥ 1` of the comparison is the restriction to rank at least two.

## Relation to other results of the Library

- `max_exponent_eq_of_isNormalizedLevel` (module `Langlands.BushnellKutzko.ConductorFormula`)
  gives `max(a, N) = N (1 + x)` for the Godement–Jacquet exponent `a` of a supercuspidal of
  normalized level `x`. When `x > 0` this forces `a = N (1 + x) > N`. When `x = 0` it gives only
  `a ≤ N`.
- `exists_firstFixedLevel_eq_of_isNormalizedLevel` (module
  `Langlands.BushnellKutzko.SwanLevelHigherRank`) gives a natural number `c` equal to the first
  fixed level with `c - N = N x` in truncated subtraction. At depth zero this says `c ≤ N`
  and does not give `c ≥ N`. The present proposition is the missing lower bound, uniformly in
  the depth.

## Sources

- C. J. Bushnell, *Hereditary orders, Gauss sums and supercuspidal representations of GL_N*,
  J. reine angew. Math. 375/376 (1987), 184–210. Source `bushnell-1987-hereditary-orders-gauss-sums`,
  SHA-256 `285eebfc66e11b0c4234c24e677ebac7472d49e113a3e3cd1e5e91c5ac364fa0`
  (PDF page = printed page − 183): §1, the Iwasawa–Tate character `ψ_F`, its conductor `𝔇_F^{-1}` and `ψ_A`,
  printed p. 190; (3.5)–(3.8), Theorem 3 and Remark (3.10), printed pp. 198–199; §5, (5.1)(i), (ii),
  (iv) and (5.2), printed p. 208.
- C. J. Bushnell and A. Fröhlich, *Non-abelian congruence Gauss sums and p-adic simple
  algebras*, Proc. London Math. Soc. (3) 50 (1985), 207–264. Source
  `bushnell-frohlich-1985-nonabelian-congruence-gauss-sums`, SHA-256
  `7ab34c7ebd9c3e5567d260de22cbc9e51598ab96a03c407376fb225496460819`
  (PDF page = printed page − 206): Theorem (3.3.8)(iv), printed p. 258,
  `ε(π, s) = N(𝔇_𝔄 𝔣(ρ))^{(1/2 - s)/n} W(ρ)` with `n² = dim_F A`.
