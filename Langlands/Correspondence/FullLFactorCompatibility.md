# Pair L-factor compatibility of full families

Author: Worker 7. This module states the pair L-factor half of the
compatibility condition for the full family `FullMap` of `Domains`. The full
family sends Frobenius-semisimple Weil–Deligne parameter classes, nonzero
monodromy allowed, to classes of irreducible admissible representations of
`GL_n(F)`, nongeneric ones included. The condition is
`L(s, π(D) × π(D')) = L(s, D ⊗ D')` for all ranks `n, n' ≥ 1`. The
representation side is the L-factor of pairs of irreducible admissible
representations that Jacquet, Piatetski-Shapiro and Shalika define through the
Langlands classification. The condition is a proposition about a given map. No
map, additive character or measure is constructed or chosen, and no part of
the correspondence is asserted. The epsilon half is not in this module (see
Scope).

## Representation side

`F : PadicField p` carries its canonical topological data and `q` is its
residue cardinality. Automorphic classes are the published
`AutomorphicClass F n`: isomorphism classes of the irreducible admissible
smooth representations of `GL_n(F)`, with carriers in universe `uA`
(`AutomorphicRelations`, `Domains`).

`IsAutomorphicPairLPolynomial F ψ ν π π' P`, for classes `π` of rank `r + 1`
and `π'` of rank `t + 1`, says `L(s, π × π') = 1 / P(q^(-s))`, as follows.
There are representatives `A` of `π` and `A'` of `π'`, and representations
`J`, `J'` with carriers in universe `max uF uA`, such that:

- `J` is equivalent to `A` and `J'` to `A'`; and
- Worker 11's published `RankinSelberg.IsLanglandsPairLPolynomial F ψ ν J J' P`
  holds.

That published relation is the definition in JPSS 1983, (9.4). Both `J` and
`J'` are Langlands quotients of tempered Langlands data. For all such data,
`P` is the L-polynomial (`IsPadicSymmetricLPolynomial`) of the pair of
standard modules. Standard modules are of Whittaker type, so the relation
also covers nongeneric `J`, `J'`. The published relation takes its
representations in universe `max uF uA`, while class representatives live in
`uA`, so the equivalence crosses carrier universes.

## Conditions

- `IsPairLCompatibleAt F ψ D D' π π'`, for parameter classes `D` of rank
  `r + 1` and `D'` of rank `t + 1`, and automorphic classes `π`, `π'` of the
  same ranks, says:
  1. a measure `ν` self-dual for `ψ` exists (`IsSelfDualMeasure` of
     `LocalConventions`); and
  2. for every such `ν`, there is a polynomial `P` with
     `IsAutomorphicPairLPolynomial F ψ ν π π' P` and
     `arithmeticPairLFactor F (parameterForget F D) (parameterForget F D') = 1/P`
     in `RatFunc ℂ`.

  The arithmetic side is `ArithmeticFactors.arithmeticPairLFactor`: the
  Artin L-factor of the tensor product of the two Weil–Deligne pairs, as a
  rational function of `X = q^(-s)`. It uses the inertia invariants of the
  kernel of the monodromy and the geometric Frobenius
  (`LocalFactor.WeilDeligne.pairLFactorClass`). `parameterForget` sends a
  Frobenius-semisimple class to its underlying Weil–Deligne class.
- `FullPairLCompatibilityAt F ψ c`, for a full map `c`: for all `r t : ℕ` and
  all parameter classes `D` of rank `r + 1` and `D'` of rank `t + 1`,
  `IsPairLCompatibleAt F ψ D D' (c D) (c D')`.
- `FullPairLCompatibility F c`: `FullPairLCompatibilityAt F ψ c` for every
  nontrivial unitary additive character `ψ` of `F`.

Ranks are written `r.succPNat` for classes and `r + 1` for representations;
these agree definitionally, so no rank casts occur.

## Sources and provenance

- Henniart 2002, §1.1, printed p.588 (PDF p.2): `G(n)` is the set of classes
  of `n`-dimensional Φ-semisimple representations of the Weil–Deligne group,
  and `A(n)` the set of classes of smooth irreducible representations of
  `GL_n(F)`. §1.2, printed pp.588–589 (PDF pp.2–3): `L(s, σ)` is the Artin
  L-function of a representation of `W'_F`, the pair factors
  `L(s, π × π')` are those of JPSS, and L-factors have the form
  `P(q^(-s))⁻¹` with `P(0) = 1`. §1.5, printed p.590 (PDF p.4), Theorem
  (iii): the full bijections satisfy
  `L(s, π_n(σ) × π_n'(σ')) = L(s, σ ⊗ σ')` for all `n, n' ≥ 1`, `σ ∈ G(n)`,
  `σ' ∈ G(n')`. This module states that identity as a condition on an
  arbitrary full map.
- Henniart 2002, §2.8, printed p.596 (PDF p.10): for `π = Σ π_i` and
  `π' = Σ π'_j` in `N[A_2] - {0}`,
  `L(s, π × π') = Π_(i,j) L(s, π_i × π'_j)`. This is the JPSS definition
  through the Langlands classification.
- JPSS 1983, (9.4), printed p.458, as recorded in Worker 11's published
  `RankinSelberg/LanglandsQuotientLFactorStatement`: `L(s, π × σ)` for any
  pair of irreducible admissible representations is defined as the factor of
  the standard modules of which they are the Langlands quotients. I did not
  re-read the JPSS scan, which has no text layer; the module takes the
  definition from the published relation.
- Tate 1979, (4.1.6), printed pp.20–21 (PDF pp.29–30): the L-factor of a
  Weil–Deligne representation is computed on the inertia invariants of the
  kernel of `N`. This is the convention of `ArithmeticFactors`.

Source files:

- `henniart-2002-characterization`, SHA-256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
- `jpss-1983-rankin-selberg`, SHA-256
  `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
- `tate-1979-number-theoretic-background`, SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.

## Interpretation

- **Additive character and measure.** The L-factor does not depend on `ψ`
  or on a measure, but the published relation is defined through zeta
  integrals that use `ψ` and a Haar measure `ν`. So the condition is stated
  at a given `ψ`, and `FullPairLCompatibility` requires it for every
  nontrivial `ψ`. A self-dual measure for `ψ` is asserted to exist, so the
  `∀ ν` clause is not vacuous, and the identity is required for every
  self-dual measure. The polynomial `P` may a priori depend on `ν`. The
  published uniqueness lemma `IsLanglandsPairLPolynomial.unique` and the
  measure independence of the arithmetic side make that dependence harmless.
- **Totality.** The polynomial `P` is asserted to exist. So the condition
  implies, and does not assume, that the JPSS L-factor of every image pair
  exists in the form the published relation requires. Its existence for all
  irreducible admissible pairs is the published, unproved
  `LanglandsPairLFactorExistenceStatement`.
- **Representatives.** The relation is existential in the representatives
  and in the equivalent representations `J`, `J'`. The JPSS L-factor is an
  invariant of the isomorphism classes, so this matches the source.
- **Both monodromies.** The parameter classes are the full domain:
  nonzero monodromy is allowed and enters the arithmetic L-factor through
  the kernel of `N`.

## Scope

- Only the L half of the full-family pair-factor condition is stated here.
  The epsilon half needs the pair epsilon factor of nongeneric
  representations, the product construction of Henniart 2002, §2.8. The
  published JPSS epsilon relations need nonzero Whittaker functionals, so
  they do not apply to nongeneric images. That epsilon factor is owned by
  task 6f0365a3 and is not yet in the Library. The full factor condition,
  L and epsilon together, will be a separate module of this task that
  imports this one.
- The module imports, and does not copy: Worker 11's
  `RankinSelberg/LanglandsQuotientLFactorStatement`
  (`IsLanglandsPairLPolynomial`), `LocalConventions`
  (`NontrivialAdditiveCharacter`, `LocalAdditiveHaarMeasure`,
  `IsSelfDualMeasure`), and this task's `Domains`, `AutomorphicRelations` and
  `ArithmeticFactors`.
- The two topology instances on `F` and on `GL_n(F)` are local and have
  explicit names, so the module can be imported together with the other
  modules of this task.

## Validation

The module compiles in the project Lean service with no errors or warnings.
There is no `sorry` and no new axiom. Every condition returns `Prop`.
