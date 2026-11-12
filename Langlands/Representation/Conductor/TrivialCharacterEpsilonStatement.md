# Existence of the epsilon factor against the trivial character of `GL_1`

Author: Worker 5032. This module defines one proposition,
`Langlands.Conductor.TrivialCharacterEpsilonStatement` (universes `uF`, `uV`).
It is a statement only: nothing here proves it, and no declaration assumes it.

## Statement

The binders are those of the published
`Langlands.Conductor.ConductorExponentStatement`
([`EssentialStatement`](EssentialStatement.md)), verbatim and in the same
order, through `IsGeneric ψ n π`:

- a field `F : Type uF` with `Field F`, `ValuativeRel F`, `TopologicalSpace F`,
  `IsNonarchimedeanLocalField F`, `T2Space F`, `TotallyDisconnectedSpace F`
  and a Borel measurable structure, with Borel structures on `GL_1(F)`, its
  (trivial) unipotent subgroup and `LeftUnipotentQuotient 0 F`; any
  characteristic is allowed and there is no `PadicField` restriction;
- `q : ℕ` equal to the cardinality of the residue field of the valuation ring
  `O`;
- `abv : AbsoluteValue F ℝ` and a uniformizer `ϖ` with `abv ϖ = q⁻¹` and
  `abv x = 1` whenever `x` is a valuation unit (the normalized absolute value);
- `ψ : UnitaryAdditiveCharacter F` with `HasIntegerConductor ψ` (`ψ` is trivial
  on `O` and on no larger fractional ideal);
- an additive Haar measure `ν` on `F` with `IsSelfDual ψ ν`;
- `n : ℕ`, `V : Type uV` (independent of `uF`) and
  `π : Representation ℂ (GeneralLinear (n + 1) F) V` with `IsGeneric ψ n π`.

The conclusion is

```
PairEpsilonFactorExists q ψ abv ν π (rankOneCharacter 1)
```

where `rankOneCharacter 1` is the trivial character of `GL_1(F)`, viewed as a
representation on `ℂ`. The case `n = 0` (`π` a representation of `GL_1(F)`) is
included.

## Source correspondence

H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika, *Rankin–Selberg
convolutions*, Amer. J. Math. 105 (1983), 367–464; registered source
`jpss-1983-rankin-selberg`, file
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`
(a scan; printed page `p` is PDF page `p − 365`). Pages read rendered: printed
385–386 (PDF 20–21), section (2.1), and printed 390–391 (PDF 25–26),
Theorem (2.7).

Theorem (2.7), printed pages 390–391, is stated for a representation `π` of
`G_r` and `π'` of `G_t`, both of Whittaker type. Part (iii) reads: "Suppose
`r = t`. Then there is a factor `ε(s, π × π', ψ)` of the form `c q^(−ns)` such
that" the functional equation (1) holds, and "Similarly, if `t ≤ r − 1`, set
`k = r − t − 1 − j`. Then" the functional equation (2) holds, "the factor
`ε(s, π × π', ψ)` being independent of `j`". The statement is the case
`π' = 1`, the trivial character of `G_1 = F^×`, so `t = 1` and `r = n + 1`.

- `PairEpsilonFactorExists q ψ abv ν π σ` (module
  [`PairEpsilonFactor`](../RankinSelberg/PairEpsilonFactor.md)) is, by
  definition, `∃ e : ℂˣ × ℤ, IsPairEpsilonFactor q ψ abv ν π σ e`. For
  `e = (c, m)` the epsilon monomial is the published
  `epsilonMonomial q c m s = c · (q^(−s))^m = c q^(−ms)`, the source's
  `c q^(−ns)` with exponent called `m` here; `c : ℂˣ` makes `c ≠ 0` explicit.
- **`n ≥ 1`.** The test rank `1` is smaller than the rank `n + 1` of `π`, so
  `IsPairEpsilonFactor` is the unequal-rank relation
  `IsUnequalRankEpsilonFactor` ([`EpsilonFactor`](../RankinSelberg/EpsilonFactor.md)).
  Its equation `UnequalRankEpsilonEquation` quantifies over every block
  decomposition `n = j + k + 1`, that is over every `j` with
  `0 ≤ j ≤ r − t − 1`, with one common `(c, m)`. This is (2.7)(iii)(2) with its
  clause "independent of `j`".
- **`n = 0`.** The ranks agree, so `IsPairEpsilonFactor` is the equal-rank
  relation `IsEqualRankEpsilonFactor`, (2.7)(iii)(1) with `r = t = 1`. Here `π`
  is a character of `F^×` and the zeta integrals involve a Schwartz–Bruhat
  function on `F`: this is Tate's local functional equation for `π`.
- Both relations require more than the monomial. They require that a compatible
  quotient measure and nonzero Whittaker functionals for `π` and for the test
  representation exist, and then, for every compatible quotient measure and
  every pair of nonzero functionals, the normalized generators `P` and `Pdual`
  of the two families of zeta values (the L-factors `L(s, π × 1)` and
  `L(1 − s, π^ι × 1)` of (2.7)(ii)), rational continuations of all the zeta
  integrals, and the functional equation with the sign `ω(−1)^(r−1)` of the
  source (`HasModelMinusOneScalar` and the published
  `NormalizedFunctionalEquation`). So the conclusion also contains the parts
  of (2.7)(ii) for the pair `(π, 1)` that the functional equation mentions;
  none of this is a premise.

## Whittaker type versus `IsGeneric`

Section (2.1), printed page 385, defines a representation of Whittaker type as
an admissible representation of finite type with `dim V*_θ = 1`, where `V*_θ`
is the space of `θ`-Whittaker functionals. The published `IsGeneric ψ n π`
says that `π` is irreducible, admissible and has a nonzero standard
`ψ`-Whittaker functional. Irreducibility gives finite type, and the source
recalls on the same page that for irreducible `π` the space `V*_θ` has
dimension `0` or `1` by Gelfand–Kazhdan [G-K]. So an `IsGeneric` representation
is of Whittaker type exactly once Whittaker multiplicity one is known, and
`IsGeneric` does not include it. The Library proves multiplicity one
(`Whittaker.multiplicityOne`, `MultiplicityOneStatement`) only for
`PadicField`. A proof of the present statement over an arbitrary `F` therefore
needs multiplicity one over `F`, or an argument that does not use it; the
Library relation asks for the functional equation for every nonzero functional
`ℓ` of `π`, which for a representation of Whittaker type is a single
functional up to scalars. The test representation `1` of `GL_1` has
`dim V*_θ = dim V = 1` and is of Whittaker type.

## The normalizations

The normalizations are those of the host `ConductorExponentStatement`, copied
unchanged: `q` is the residue cardinality, `abv` is the normalized absolute
value fixed by `abv ϖ = q⁻¹` and `abv = 1` on units, `ψ` has conductor `O`,
and `ν` is self-dual for `ψ`, the measure for which the published relation is
meant to define the JPSS factor ([`EpsilonFactor`](../RankinSelberg/EpsilonFactor.md)
records that the sources use the self-dual measure). The pair `(π, rankOneCharacter 1)` and
the parameters `q ψ abv ν` are exactly those for which the host asserts
`IsPairEpsilonFactor q ψ abv ν π (rankOneCharacter 1) (c, (m : ℤ))`. So the
exponent `m` produced here is the one the host constrains; because the
pair epsilon factor is unique for `q > 1` (published
`IsPairEpsilonFactor.unique`), the host's `(c, m)` must be the one supplied here. The uniformizer `ϖ` occurs
only to pin down `abv`; it is not used in the conclusion.

## Why the exponent is only an integer

The source's factor `c q^(−ns)` has an integer exponent and Theorem (2.7)
asserts nothing about its sign. The statement accordingly concludes only
`m : ℤ`. That `m ≥ 0` for irreducible generic `π`, and that `m` is the
conductor, are part of the host `ConductorExponentStatement` (`m : ℕ` there),
derived in JPSS 1981, (5.3) and Theorem (5.1), from the dual comparison of
essential vectors. They are not part of this statement.

## Why this statement is needed

The Library's proved existence results for epsilon factors quantify over
`PadicField` only: `genericPairEpsilonFactorExists` in
`Langlands.Representation.RankinSelberg.PadicSymmetricEpsilonFactor`, and the
statements `Theorem27Statement` (module `FunctionalEquationStatement`),
`PairEpsilonNormalizationStatement` and
`LanglandsPairEpsilonFactorExistenceStatement` all fix `F : PadicField p`. The
host statement covers every nonarchimedean local field, including those of
positive characteristic, so it needs this existence result over arbitrary `F`.
A proof must not import the p-adic-only results.

## Imports

`Langlands.Representation.Conductor.EssentialStatement` (for the host's
binders, `HasIntegerConductor`, `IsSelfDual`, `IsGeneric` and
`rankOneCharacter`) and `Langlands.Representation.RankinSelberg.PairEpsilonFactor`
(for `PairEpsilonFactorExists`). `Langlands.GeneralLinear.Iwasawa` is opened
as in the host module.
