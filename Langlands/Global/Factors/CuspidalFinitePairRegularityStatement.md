# Regularity of the finite pair L-factors of unitary cuspidal realizations on `Re s ≥ 1`

Lean module: `Langlands.Global.Factors.CuspidalFinitePairRegularityStatement`.
It contains one proposition, `Langlands.Global.CuspidalFinitePairRegularityStatement`,
and no proofs.

## Statement

```lean
def CuspidalFinitePairRegularityStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r t : ℕ) (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t),
    HasUnitaryCentralCharacter T → HasUnitaryCentralCharacter T' →
  ∀ (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (h : HasIrreducibleAdmissibleComponents P) (h' : HasIrreducibleAdmissibleComponents P')
    (c : CuspidalPairPoles.FinitePairLChoice P P' h h') (v : FinitePlace F) (s : ℂ),
    1 ≤ s.re →
      (c.lPolynomial v).eval (RankinSelberg.spectralPoint (residueCardinality v) s) ≠ 0
```

## Notation

All objects are the published ones used by the pole statement
`Langlands.Global.CuspidalPairPoleStatement` (module
`Langlands.Global.Factors.CuspidalPairPoleStatement`).

- `F : Type u` is a number field with the standing assumption
  `CompactSpace (AdeleQuotient F)`.
- `T`, `T'` are actual irreducible cuspidal realizations of `GL_(r+1)`,
  `GL_(t+1)` (`CuspidalOperatorRealization`). Each has a unitary central
  character (`HasUnitaryCentralCharacter`: a central character of norm `1`).
- `P`, `P'` are spectral presentations of `T`, `T'` in the factor universe `uQ`,
  with irreducible admissible finite local components at every finite place
  (`CuspidalPairFunctionalEquation.HasIrreducibleAdmissibleComponents`).
- `c : CuspidalPairPoles.FinitePairLChoice P P' h h'` chooses, at every finite
  place `v`:
  - a nontrivial additive character and a self-dual measure of `F_v`;
  - a polynomial `c.lPolynomial v` with
    `Correspondence.IsAutomorphicPairLPolynomial` for the classes of the two
    local components.

  This is the pair L-polynomial `P_v` of `(Π_v, Π'_v)`, normalized through the
  Langlands classification (the standard modules of the two components), with
  `L(s, Π_v × Π'_v) = P_v(q_v^(-s))⁻¹` (`FinitePairLChoice.finiteL`).
- `residueCardinality v` is `q_v`, and `RankinSelberg.spectralPoint q s = q^(-s)`.

## Meaning

For every finite place `v` and every `s` with `Re s ≥ 1`, `P_v(q_v^(-s)) ≠ 0`.
Equivalently, the local pair L-factor `L(s, Π_v × Π'_v)` of two unitary cuspidal
realizations has no pole in the closed half-plane `Re s ≥ 1`. It never vanishes,
being the inverse of a polynomial value.

- No existence claim is made: the statement quantifies over the finite L-data,
  whose existence is part of the pole statement.
- The statement concerns every finite place, including those where the
  presentations are ramified.

## Correspondence with the source

Getz–Hahn, Theorem 11.5.2, printed p.305 (PDF 316): "If `π` and `π'` are
unitary, then `L(s, π × π')` is holomorphic and nonzero for `Re(s) ≥ 1`." There
`π`, `π'` are irreducible admissible generic representations of the local
general linear groups. In the non-Archimedean case
`L(s, π × π') = P_(π,π')(q^(-s))⁻¹`, (11.21) on the same page, and the theorem
follows from Proposition 11.5.1.

The statement applies the theorem to the local components at finite places of
two unitary cuspidal realizations. GH use these components in Theorem 11.7.1,
p.309 (PDF 320). They are generic and unitarizable; in the Library these are the
proved `Automorphic.cuspidalUnitaryLocalGenericity` and
`Automorphic.cuspidalUnitaryLocalUnitarity`.

The only difference from the source is the normalization of the L-polynomial.

- GH's `P_(π,π')` is the JPSS polynomial of the generic pair itself; in the
  Library this is `IsPadicSymmetricLPolynomial`.
- The statement uses the L-polynomial of the pole statement's finite data. That
  polynomial is defined through the standard modules
  (`IsAutomorphicPairLPolynomial`, via `IsLanglandsPairLPolynomial`).
- For generic representations the two agree by Jacquet, Piatetski-Shapiro and
  Shalika, *Rankin-Selberg convolutions* (1983), Proposition (9.4), display (4),
  printed p.458, published as
  `RankinSelberg.GenericLanglandsQuotientLFactorStatement`.

## Relation to published statements

- `Langlands.RankinSelberg.UnitaryGenericLPolynomialNonvanishingStatement` is
  the local p-adic form of Theorem 11.5.2 for `IsPadicSymmetricLPolynomial`.
  Combined with the local genericity and unitarity of cuspidal components and
  with JPSS (9.4)(4) for the change of normalization, it should imply this
  statement. No such reduction is stated or proved here.
- `Langlands.Automorphic.CuspidalArchimedeanPairRegularityStatement` is the
  archimedean counterpart, for the archimedean denominators of the pole
  statement. The two together say that the local factors removed from a
  completed pair L-function of unitary cuspidal realizations are regular on
  `Re s ≥ 1`. Then the order at `s = 1` of the partial L-function equals that of
  the completed one.
- Getz–Hahn, p.309 (PDF 320), apply Theorem 11.5.2 to the local factors at all
  places of representations trivial on `A_GL`, before Theorem 11.7.1. On the
  same page they say that Theorem 11.7.2 (strong multiplicity one) is a
  consequence of Theorems 11.5.2 and 11.7.1 (Exercise 11.6).

## Sources

- J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations*,
  GTM 300, Springer, 2024, registered as
  `getz-hahn-2024-automorphic-representations`. In Chapter 11, PDF page =
  printed page + 11. Cited: Theorem 11.5.2 and (11.21), p.305 (PDF 316);
  the paragraph before Theorem 11.7.1, Theorems 11.7.1 and 11.7.2, p.309
  (PDF 320).
- H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg
  convolutions*, Amer. J. Math. 105 (1983), 367–464, registered as
  `jpss-1983-rankin-selberg`. Cited: Proposition (9.4), display (4), p.458.
