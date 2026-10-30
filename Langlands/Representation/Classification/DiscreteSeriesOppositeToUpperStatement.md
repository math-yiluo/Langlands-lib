# Same-sigma opposite-to-upper discrete-series induction comparison

Author: Worker 470. Worker 1058 updated the proof status for the 2026-10-29
documentation audit; the Lean file is unchanged.

`Langlands.GLTemperedDiscreteSeriesOppositeToUpperStatement` is a proposition
definition. It isolates one implication needed by the published
`GLTemperedDiscreteSeriesSummandStatement`. This statement pair proves no
analytic or representation-theoretic implication. The companion module
`Langlands.Representation.Classification.DiscreteSeriesOppositeToUpperProof`
proves the proposition: `Langlands.glTemperedDiscreteSeriesOppositeToUpper`
has exactly the type
`GLTemperedDiscreteSeriesOppositeToUpperStatement.{uF, uV, uW}`, with no
further hypotheses.

## Exact statement and universes

The quantifiers and hypotheses are those of the summand statement, through
its square-integrability hypothesis. Fix a prime `p` with `Fact p.Prime`, an
arbitrary `PadicField.{uF} p`, its supplied `T : F.TopologicalData`, a positive
total rank `n`, and an actual ordered block shape `B`. Install `T.topology`
and its product-Levi topological group. Put

```text
G = GeneralLinear n F.Carrier,
M = B.Levi F.Carrier,
Q = M / Subgroup.center M.
```

Quantify over every measurable space on `Q` with `BorelSpace`, every Haar
measure `μ` on that quotient, independent complex carriers `V : Type uV`
and `W : Type uW`, and actual representations `π` of `G` on `V` and `σ`
of the full product Levi `M` on `W`. Assume

```text
IsIrreducible π, T.IsTempered π,
IsIrreducible σ, IsSquareIntegrableModCenter σ μ.
```

For these fixed inputs, the conclusion is exactly

```text
(∃ j : π.IntertwiningMap (T.normalizedOppositeParabolicInduced B σ),
    Function.Injective j) →
  (Representation.IsSemisimpleRepresentation
      (T.normalizedOppositeParabolicInduced B σ) ∧
   ∃ j : π.IntertwiningMap (T.normalizedParabolicInduced B σ),
      Function.Injective j).
```

The field universe `uF`, ambient carrier universe `uV`, and Levi carrier
universe `uW` are independent. Both induced carriers are actual spaces of
`W`-valued functions and lie in `Type (max uF uW)`; the intertwiners allow
this universe to differ from `uV`. The coefficient field is `ℂ`.
Irreducibility includes nontriviality. The analytic predicates already
include admissibility and smoothness, so those source hypotheses have not
been omitted. No topology on either representation carrier is prescribed.

The representation `σ` is the identical given action on the full product
Levi in both inductions. There is no external tensor-product hypothesis.
The conclusion requires an actual injective intertwiner, rather than an
occurrence predicate. Semisimplicity is Mathlib's complemented lattice of
invariant subspaces. Upper semisimplicity remains in
`GLTemperedInductionStatement` and is not a conclusion of this proposition.
No full equivalence of induced representations is asserted.

## Actual function spaces and normalization

The imports use the published `Induction/Parabolic` and
`Induction/OppositeParabolic` constructions. Write `P` for the actual upper
block parabolic, `Pbar` for its actual opposite, and `m` for the corresponding
projection to the same product Levi. The explicit upper block modulus is

```text
δ(m) = ∏_(i<j) |det m_i|^(B.size j) / |det m_j|^(B.size i).
```

The absolute value is residue-normalized. Its positive half character is
`T.leviHalfModulus B`. The two covariance laws and the common action are

```text
f(p g)    = δ(m(p))^(1/2)  • σ(m(p))(f(g)),
f(pbar g) = δ(m(pbar))^(-1/2) • σ(m(pbar))(f(g)),
(g₀ · f)(x) = f(x g₀).
```

The functions have a uniform open right stabilizer. The existing wrappers
prove these laws and smoothness. Opposite induction uses the inverse of the
upper positive half character, inflated along the actual opposite projection.
It does not change the inducing action. Identification of the explicit
determinant modulus with the Haar modulus of conjugation on the upper
radical, and its inverse with that on the opposite radical, is a separate
formal comparison needed to apply the printed induction results.

Conjugating the opposite parabolic to an upper parabolic transports and
reverses the Levi action. The generic `conjugateSmoothInducedEquiv` therefore
does not by itself establish this implication for the unchanged `σ`.

## Analytic convention bridge

`IsSquareIntegrableModCenter σ μ` means admissibility, a smooth scalar
unitary central character, and square integrability of every absolute smooth
matrix coefficient on the actual quotient by the full center.
`IsTemperedModCenter` replaces square integrability by membership in
`L^(2+ε)` for every real `ε > 0`. The ambient predicate `T.IsTempered π`
requires the latter for every Borel Haar measure on the ambient central
quotient. The published Haar-existence helpers in `Tempered` and
`TemperedInductionStatement` ensure that these measure quantifications are
nonvacuous.

Silberger's temperedness is defined through tempered coefficient functions.
Theorem 4.5.1 and the following definition, printed pp.183–184, identify
the relevant locally constant coefficients with the weak bound
`|c(g)| ≤ C Ξ(g) (1 + length(g))^r`. The bridge to the Library's analytic
predicate is the derived specialization described in
[TemperedInductionStatement](TemperedInductionStatement.md). It applies to
`GL_n(F)` and to the actual product Levi, without factoring `σ`:

1. The full center of each general linear factor is split, and the full
   center of the product is the product of those centers. Cartan chambers,
   moduli and spherical functions have product descriptions on this group;
   a sum of factor lengths suffices. With unitary scalar central character,
   absolute coefficients descend to the full central quotient.
2. Waldspurger I.1(5), p.241, compares Cartan double-coset volumes to
   `d(a)^(-1)`, where `d(a) = δ₀(a) ≤ 1` on the closed chamber. Lemma II.1.1,
   p.251, bounds `Ξ(a)` by `d(a)^(1/2)` times a polynomial in length. Thus a
   weakly bounded coefficient has `L^(2+ε)` integral bounded by a chamber
   lattice sum of `d(a)^(ε/2)` times a polynomial. Modulo the full center,
   exponential decay dominates that polynomial. Rank-zero factors contribute
   compact directions; local constancy supplies measurability.
3. Conversely, Waldspurger I.4.1, p.245, and the argument of III.2.2, p.266,
   realize a normalized Jacquet exponent in a coefficient sufficiently deep
   in a chamber. A growing exponent on a rational chamber direction would,
   on powers of a suitable element and disjoint compact-open cosets, give
   contributions proportional to
   `δ_P(a)^(ε/2) |χ(a)|^(2+ε)`. For sufficiently small positive `ε` these
   contradict integrability. The exponent weak inequalities then yield
   the weak coefficient bound by III.2.2. The same reductive argument applies
   on the product group.
4. Borel Haar measures on these locally compact second-countable quotients
   differ by a positive finite scalar. Finite `L^r` membership is invariant
   under that change. Hence the supplied Levi measure and every ambient
   measure have the scope required here.

Silberger Theorem 4.5.10(1)–(2), pp.188–189, supplies the source
square-integrable-to-tempered step coefficient by coefficient for the full
Levi. The published theorem `glLeviDiscreteSeriesTempered` supplies the
same-measure analytic implication in the Library. These observations explain
the convention correspondence; this statement pair does not implement the
Cartan, exponent or Haar-modulus comparisons.

## Source provenance and focused derivation

The sources are the registered retained originals:

| Original | Exact passages read | Role |
| --- | --- | --- |
| A. J. Silberger, *Introduction to Harmonic Analysis on Reductive p-adic Groups* (1979), `silberger-1979-harmonic-analysis`, SHA256 `b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc` | Theorem 4.5.1 and following definition, pp.183–184; Theorem 4.5.10, pp.188–189 | Tempered coefficient convention and square-integrable-to-tempered source step. |
| Same original | Lemma 4.5.15, p.191; Theorem 4.5.18(3) and its proof, p.193; Theorem 3.3.1 and its proof, pp.126–127 | Complete reducibility for either parabolic and the same-`σ` comparison isolated here. |
| J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra* (2003), `waldspurger-2003-plancherel`, SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7` | I.1(5), p.241; I.4.1, p.245; II.1.1, p.251; III.2 and III.2.2, pp.265–266 | Cartan volumes, Jacquet coefficient asymptotics, spherical-function estimates, and weak exponent criterion for the analytic bridge. |

Silberger's one-based PDF page is the printed page plus six; Waldspurger's
is the printed page minus 234. The decisive formulas were checked in page
images. No errata note for either registered source was found in the current
Library during preparation.

This is a derived, focused consequence of the source results, specialized
to the supplied standard block shape over a finite extension of `Q_p`.
Lemma 4.5.15 applies to any parabolic pair, so, after the normalization and
analytic comparisons, it supplies opposite semisimplicity from temperedness
of `σ`. Theorem 4.5.18(3) explicitly has the same discrete-series `σ` in
both inductions and identifies `π` as a summand of each when its equivalent
Jacquet conditions hold. An opposite embedding gives the corresponding
Jacquet quotient through actual first adjointness, and hence the required
class occurrence. This explains the narrower implication stated here; it
does not make the parent summand proposition a hypothesis or input of this
statement. The published theorem `Langlands.glTemperedDiscreteSeriesSummand`
proves that parent proposition and uses
`glTemperedDiscreteSeriesOppositeToUpper`.

Theorem 4.5.18's proof refers to Theorem 3.3.1 with a temperedness condition
on its auxiliary module and on the analogous Jacquet component. The printed
Theorem 3.3.1 itself assumes cuspidal inducing data, so the cuspidal theorem
alone does not prove this target. The companion proof implements the tempered
adaptation. Its auxiliary modules are the scalar layers of the opposite
Jacquet module of `π`. They are tempered by
`glTemperedOppositeJacquetScalarLayer`, and the isotypic projector of
`glTemperedDiscreteSeriesIsotypic` turns the given quotient `σ` into a
subrepresentation. Second adjointness then gives a nonzero map from upper
induction onto `π`. Semisimplicity of upper induction, from
`isSemisimple_bothInduced_of_squareIntegrable`, splits that map into the
required upper embedding.

## Proof status

The companion theorem `Langlands.glTemperedDiscreteSeriesOppositeToUpper`, in
`Langlands.Representation.Classification.DiscreteSeriesOppositeToUpperProof`,
proves the exact proposition. It keeps `uF`, `uV` and `uW` independent and
adds no hypotheses. It constructs opposite semisimplicity and the injective
upper map on the actual function spaces, keeping the given `σ` in both
inductions. [The proof's documentation](DiscreteSeriesOppositeToUpperProof.md)
lists each published theorem the proof uses.

The proof does not use `GLTemperedInductionStatement` or the parent summand
theorem. No assumed proof package or replacement for the fixed inducing
representation is an input to this statement.
