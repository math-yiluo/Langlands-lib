# Epsilon-factor conductors of irreducible pairs through Langlands data

Author: Worker 18 (task `6f0365a3-7419-4804-b209-3fc348b878de`).

This module extends the epsilon-factor conductors of
`Conductor.GenericEpsilonConductor` from generic to arbitrary irreducible smooth
representations. It defines:

- the epsilon exponent `f(π × σ, ψ)` of an irreducible pair;
- the conductor of the pair, `f(π × σ)`;
- the conductor `f(π) = f(π × 1)` of an irreducible representation.

They are integers read off from the epsilon factor through square-integrable Langlands data
that the Library already constructs,
`RankinSelberg.langlandsPairEpsilonFactorOfClassification`. That constructor needs the
square-integrable exhaustion and classification propositions of
`Classification/MultisegmentClassificationStatement`. These propositions are not proved in
the Library. Every definition here therefore takes them as explicit arguments. All other
inputs of the constructor are proved: the block epsilon factors come from
`RankinSelberg.squareIntegrableDataEpsilonExistence`, and the measure is the actual self-dual
Haar measure. No default value, chosen measure or other existence hypothesis is introduced.

## Setting and normalization

The setting is that of `Conductor.GenericEpsilonConductor`. The local instances, the
private `valuative_nonarchimedean` proof and the conventions below are copied from that
module.

- **Field.** `F : PadicField p`, for any prime `p` and field universe `uF`, with the
  canonical normed field, valuation, local-field and Borel structures.
- **Spectral variable.** `e = (c, m) : ℂˣ × ℤ` represents the monomial `c q^(-ms)`, with
  `q = F.canonicalTopologicalData.residueCardinality`. This is the convention of
  `RankinSelberg.IsLanglandsPairEpsilonFactor`.
- **Representations.** `π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (r + 1) F.Carrier)`
  and `σ : SmoothRep.{0, uF, max uF uW} ℂ (GeneralLinear (t + 1) F.Carrier)`. Both are
  assumed `Representation.IsIrreducible`; no genericity is assumed. The ranks `r + 1`,
  `t + 1` are arbitrary positive numbers, so rank one is included, and either rank order is
  allowed. The carrier universes `max uF uV` and `max uF uW` are those of the published
  constructor.
- **Classification inputs.** `hexπ`, `hexσ` are
  `SquareIntegrableLanglandsExhaustion F F.canonicalTopologicalData` at universes `uV` and
  `uW`: every irreducible smooth representation of positive rank is the Langlands head of a
  square-integrable datum. `hclπ`, `hclσ` are `SquareIntegrableLanglandsClassification` at the
  same universes: two data have isomorphic irreducible quotients exactly when their blocks
  match up to permutation and isomorphism (Henniart 2002, §2.8).
- **Additive character and measure.** `ψ` is any `UnitaryAdditiveCharacter`. The measure is
  the published `Correspondence.localSelfDualHaar F ψ`, chosen only from the proved existence
  and uniqueness theorem for self-dual measures. Because of that uniqueness, every
  characterization below holds at every `ν` with `IsSelfDual ψ ν`.
- **Additive conductor.** `c(ψ)` is `F.canonicalTopologicalData.additiveConductor ψ`, the
  largest `n` with `ψ` trivial on `𝔭^(-n)`. This is Bushnell–Henniart–Kutzko's `c(ψ)`.

## Definitions

`langlandsPairEpsilonCoefficientExponent F ψ π σ hπ hσ hexπ hexσ hclπ hclσ : ℂˣ × ℤ` is the
value of `langlandsPairEpsilonFactorOfClassification` at `ν = localSelfDualHaar F ψ`. Its
block input is `squareIntegrableDataEpsilonExistence` at the same measure, packaged with its
self-duality proof by the private `selfDualPoint`. It is the pair `(c, m)` with
`ε(s, π × σ, ψ) = c q^(-ms)`, where `ε(s, π × σ, ψ)` is the product, over all pairs of blocks
of square-integrable data presenting `π` and `σ`, of the JPSS epsilon factors of the blocks.

`langlandsPairEpsilonExponent … : ℤ` is the exponent `m`. This is BHK's `f(π × σ, ψ)`.

`langlandsPairConductor … : ℤ` is

`langlandsPairEpsilonExponent … - ((r + 1) * (t + 1)) * c(ψ)`.

This is BHK's `f(π × σ)`, from `f(π₁ × π₂, ψ) = n₁ n₂ c(ψ) + f(π₁ × π₂)` with `n₁ = r + 1` and
`n₂ = t + 1`.

`trivialRankOneObject F` is the published `Correspondence.rankOneCharacterObject F 1`: the
trivial character of `GL_1(F)` acting on the lifted line `ULift ℂ`, as an object of
`SmoothRep.{0, uF, max uF uV}`. `trivialRankOneObject_isIrreducible` proves its
irreducibility from `FiniteRepresentation.characterLine_isIrreducible`.

`langlandsConductor F ψ π hπ hex hcl : ℤ` is `langlandsPairConductor` of `π` against
`trivialRankOneObject F`, with both classification inputs at universe `uV`. So it is
`f(π × 1)`, which equals `m - (r + 1) c(ψ)` for the epsilon factor `c q^(-ms)` of `π × 1`.

Each definition takes `ψ` as an explicit argument. Independence of `ψ` is a separate
obligation (see below).

## Proved properties

Pairs:

- `langlandsPairEpsilonCoefficientExponent_isLanglands`: at every self-dual `ν`, the
  constructed data satisfy `IsLanglandsPairEpsilonFactor F ψ ν π σ`. The proof identifies `ν`
  with `localSelfDualHaar F ψ` by `Correspondence.eq_localSelfDualHaar` and uses the
  certificate of the constructor.
- `langlandsPairEpsilonCoefficientExponent_eq`: every `e` with
  `IsLanglandsPairEpsilonFactor F ψ ν π σ e` at a self-dual `ν` equals the constructed data,
  by the published uniqueness `IsLanglandsPairEpsilonFactor.unique`.
- `langlandsPairConductor_eq`: for every such `e`,
  `f(π × σ) = e.2 - (r + 1)(t + 1) c(ψ)`.
- `langlandsPairConductor_eq_epsilonExponent`: if `ψ` has conductor `𝔒`
  (`Conductor.HasIntegerConductor ψ`), then `f(π × σ) = f(π × σ, ψ)`. The proof uses
  `additiveConductor_eq_zero_of_hasIntegerConductor` from `GenericEpsilonConductor`.
- `langlandsPairEpsilonExponent_eq_sum`: let `d`, `d'` be square-integrable data presenting
  `π` and `σ` (`d.IsLanglandsQuotient π`, `d'.IsLanglandsQuotient σ`), and let `b i j` be any
  epsilon factors of the block pairs at a self-dual `ν`
  (`IsPadicRankEpsilonFactor F ψ ν (d.blocks i) (d'.blocks j) (b i j)`). Then
  `f(π × σ, ψ) = ∑ i, ∑ j, (b i j).2`. The proof applies the third clause of
  `IsLanglandsPairEpsilonFactor` to `d`, `d'` and uses
  `IsSquareIntegrableDataEpsilonFactor.unique` against `epsilonFactorProduct b`.
- `langlandsPairConductor_eq_sum`: in the same situation,
  `f(π × σ) = ∑ i, ∑ j, ((b i j).2 - n_i n'_j c(ψ))`, where `n_i = d.shape.size i` and
  `n'_j = d'.shape.size j` are the block ranks. The proof expands
  `(r + 1)(t + 1) = (∑ n_i)(∑ n'_j)` with `BlockShape.sum_eq` and regroups the sums.
- `isLanglandsPairEpsilonFactor_of_equiv`: the relation `IsLanglandsPairEpsilonFactor` is
  transported along equivalences `π ≃ π₂`, `σ ≃ σ₂` of representations in the same
  universes. The private `isIrreducibleQuotient_of_equiv_target` transports irreducibility
  through the simple-module characterization and composes the quotient map with the
  equivalence.
- `langlandsPairEpsilonCoefficientExponent_congr_equiv` and
  `langlandsPairConductor_congr_equiv`: the data and the conductor are unchanged when `π` and
  `σ` are replaced by equivalent irreducible representations.
- `langlandsPairEpsilonCoefficientExponent_eq_generic` and `langlandsPairConductor_eq_generic`:
  assume the published, unproved statement
  `RankinSelberg.GenericLanglandsPairEpsilonFactorComparisonStatement` at universes
  `uF, max uF uV, max uF uW`. If `π` and `σ` are moreover `Whittaker.IsGeneric ψ`, then the
  data and the conductor through Langlands data equal the generic ones,
  `genericPairEpsilonCoefficientExponent` and `genericPairConductor`. The proof feeds the
  Langlands certificate to the comparison statement and applies
  `genericPairEpsilonCoefficientExponent_eq`. The comparison statement is a hypothesis; these
  theorems do not prove it.

Single representations:

- `langlandsConductor_eq`: if `IsLanglandsPairEpsilonFactor F ψ ν π 1 (c, m)` at a self-dual
  `ν`, then `f(π) = m - (r + 1) c(ψ)`.
- `langlandsConductor_eq_of_hasIntegerConductor`: if moreover `ψ` has conductor `𝔒`, then
  `f(π) = m`, the JPSS 1981 normalization.
- `exists_isLanglandsPairEpsilonFactor_langlandsConductor`: at every self-dual `ν` there is
  `c` with `IsLanglandsPairEpsilonFactor F ψ ν π 1 (c, f(π) + (r + 1) c(ψ))`.
- `langlandsConductor_congr_equiv`: `f(π)` is unchanged when `π` is replaced by an
  equivalent irreducible representation.
- `trivialRankOneObjectEquiv`: an equivalence from the scalar trivial character
  `rankOneCharacter 1` used by `genericConductor` to `trivialRankOneObject F`, given by the
  inverse of `ULift.moduleEquiv`.
- `langlandsConductor_eq_genericConductor`: under the same comparison statement at
  universes `uF, max uF uV, max uF uV`, for generic `π`, `f(π)` equals
  `genericConductor F ψ π.representation hπg`. The trivial line is generic by
  `UniformRankOneTwist.isGeneric_rankOneCharacter_one`, transported along
  `trivialRankOneObjectEquiv` by `Whittaker.isGeneric_iff_of_equiv`; the two trivial
  characters are then exchanged by `genericPairConductor_congr_equiv`.

## Sources and correspondence

- Henniart, *Une caractérisation de la correspondance de Langlands locale pour GL(n)*,
  Bull. Soc. Math. France 130 (2002), 587–602. Literature ID
  `henniart-2002-characterization`, SHA-256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
  §2.8, printed p.596 (PDF page 10): an irreducible representation is the unique irreducible
  quotient `J(π₁, …, π_r)` of `i(π₁, …, π_r)` for essentially square-integrable `π_i` with
  decreasing exponents, and for `π = ∑ π_i`, `π' = ∑ π'_j`,
  `ε(s, π × π') = ∏_{i,j} ε(s, π_i × π'_j, ψ)`. This is the epsilon factor that
  `IsLanglandsPairEpsilonFactor` encodes and that this module reads off; the block sum
  `langlandsPairEpsilonExponent_eq_sum` is the exponent form of this product.
- Bushnell, Henniart and Kutzko, *Local Rankin–Selberg convolutions for GL_n: explicit
  conductor formula*, J. Amer. Math. Soc. 11 (1998), 703–730. Literature ID
  `bhk-1998-explicit-conductor`, SHA-256
  `5f3c996bc6be89966f3a39ecba68f58926137096bc8fce9b489f11be18167657`.
  - Introduction, printed p.703 (PDF page 1): for irreducible smooth `π₁`, `π₂` (not
    necessarily generic), `c(ψ)` is the largest `c` with `𝔭^(-c) ⊂ Ker ψ`,
    `ε(π₁ × π₂, s, ψ) = ε(π₁ × π₂, 0, ψ) q^(-f(π₁ × π₂, ψ) s)`, and
    `f(π₁ × π₂, ψ) = n₁ n₂ c(ψ) + f(π₁ × π₂)` with `f(π₁ × π₂)` independent of `ψ`.
  - Printed p.704 (PDF page 2): `f(π) = f(π × 1_F)` for the Godement–Jacquet conductor,
    where `1_F` is the trivial representation of `GL_1(F)`.

Provenance: the pair definitions transcribe BHK's `f(π × σ, ψ)` and `f(π × σ)` for the
Library's epsilon factor through Langlands data (Henniart 2002, §2.8). The definition
`f(π) = f(π × 1)` is derived, as in `GenericEpsilonConductor`: the Library has no
Godement–Jacquet epsilon factor for general `GL_n`, so the pair factor against the trivial
character of `GL_1` is used, following BHK p.704. The comparison with the Godement–Jacquet
conductor is not proved.

## Scope and open obligations

- The exhaustion and classification propositions remain hypotheses of every definition. The
  conductors become unconditional once those propositions are proved.
- Not proved here:
  - independence of `ψ` (BHK p.703);
  - nonnegativity of `f(π × σ)` and `f(π)`;
  - the generic comparison `GenericLanglandsPairEpsilonFactorComparisonStatement`, used only
    as a hypothesis;
  - comparison with the Godement–Jacquet conductor;
  - identification of the block terms of `langlandsPairConductor_eq_sum` with the generic
    conductors of the blocks as Lean terms.

## Imports

- `Conductor.GenericEpsilonConductor`: the generic conductors,
  `additiveConductor_eq_zero_of_hasIntegerConductor`, and `isGeneric_rankOneCharacter_one`
  through its imports.
- `RankinSelberg.LanglandsPairEpsilonBlockExistence`: `squareIntegrableDataEpsilonExistence`.
- `RankinSelberg.LanglandsFactorDescent`: `langlandsPairEpsilonFactorOfClassification`.
- `RankinSelberg.GenericLanglandsPairEpsilonFactorComparisonStatement`: the comparison
  statement used as a hypothesis.
- `Correspondence.RankOneExistence`: `rankOneCharacterObject`.

All imports are published Library modules. The module adds no axioms. The inspected theorem
`langlandsConductor_eq_genericConductor` uses only `propext`, `Classical.choice` and
`Quot.sound`. `lean_check` reports 0 errors and 0 warnings.
