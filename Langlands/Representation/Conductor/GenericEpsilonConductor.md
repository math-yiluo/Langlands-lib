# Epsilon-factor conductors of generic p-adic representations and pairs

Author: Worker 18 (task `6f0365a3-7419-4804-b209-3fc348b878de`).

This module constructs the conductor exponents defined by epsilon factors:

- the epsilon exponent `f(π × σ, ψ)` of a generic pair;
- the conductor of the pair, `f(π × σ)`;
- the conductor `f(π) = f(π × 1)` of a generic representation.

They are integers, read off from the epsilon factor that the Library already
constructs from the proved JPSS functional equations. No existence hypothesis,
chosen measure or default value enters the definitions. Before this module, the
Library had least-level and newvector constructors
(`Conductor.Definitions`, `Conductor.ClassLevel`, `Conductor.RankOne`). It did not
define the conductor through epsilon factors: `Conductor/ClassLevel.md` says
"The general epsilon-factor conductor is not defined by this function".

## Setting and normalization

- **Field.** `F : PadicField p`, for any prime `p` and field universe `uF`, with the
  canonical structure. The topology is that of `F.canonicalNormedField`; the
  valuation and local-field structure are those of `F.canonicalTopologicalData`;
  the measurable structure is Borel. These are the local instances of
  `RankinSelberg/PadicSymmetricEpsilonFactor`, whose constructors are reused here.
  The private `valuative_nonarchimedean` proof is copied from that module. It
  derives the nonarchimedean additive structure from the open-submodule basis and
  adds no assumption.
- **Residue cardinality and spectral variable.** `q` is
  `F.canonicalTopologicalData.residueCardinality`. The absolute value is
  `normalizedAbsoluteValue F.canonicalTopologicalData`, so `|ϖ| = q⁻¹`. The
  epsilon monomial is `c q^(-ms)`.
- **Representations.** `π` acts on a complex module `V` (universe `uV`) through
  the actual group `GL_(r+1)(F)`, and `σ` acts on `W` (universe `uW`) through
  `GL_(n+1)(F)`. The ranks `r + 1` and `n + 1` are arbitrary and positive, so rank
  one is included. Either rank order is allowed. Both members are assumed
  `Whittaker.IsGeneric` for the same character `ψ`: irreducible, admissible, and
  with a nonzero standard Whittaker functional.
- **Additive character and measure.** `ψ` is any `UnitaryAdditiveCharacter`
  (continuous, nontrivial, unit-circle valued). The measure is the actual
  self-dual additive Haar measure of `ψ` for the plus-sign Fourier transform. It
  is the published `Correspondence.localSelfDualHaar F ψ`, which is chosen only
  from the proved existence and uniqueness theorem
  `Correspondence.existsUnique_localSelfDualMeasure`. No new measure is chosen
  here. Because of that uniqueness, every characterization below holds at every
  `ν` with `IsSelfDual ψ ν`.
- **Additive conductor.** `c(ψ)` is
  `F.canonicalTopologicalData.additiveConductor ψ`, the published Tate integer
  `n(ψ)` (`HarmonicAnalysis/Conductor`): the largest `n` with `ψ` trivial on
  `𝔭^(-n)`. This is exactly Bushnell–Henniart–Kutzko's `c(ψ)`, "the largest
  integer `c` such that `𝔭^(-c) ⊂ Ker ψ`".

## Definitions

`genericPairEpsilonCoefficientExponent F ψ π σ hπ hσ : ℂˣ × ℤ` is the published
`genericSymmetricEpsilonData` evaluated at `localSelfDualHaar F ψ`. This is the
coefficient `c` and exponent `m` of `ε(s, π × σ, ψ) = c q^(-ms)`. The pair is read
with the larger rank first, the JPSS (2.12) convention used by
`IsPadicSymmetricEpsilonFactor`; at equal ranks the given order is kept.

`genericPairEpsilonExponent F ψ π σ hπ hσ : ℤ` is the exponent component. This is
BHK's `f(π × σ, ψ)`.

`genericPairConductor F ψ π σ hπ hσ : ℤ` is

`genericPairEpsilonExponent F ψ π σ hπ hσ - ((r + 1) * (n + 1)) * c(ψ)`.

This is BHK's `f(π × σ)`, from their identity
`f(π₁ × π₂, ψ) = n₁ n₂ c(ψ) + f(π₁ × π₂)` with `n₁ = r + 1` and `n₂ = n + 1`.

`genericConductor F ψ π hπ : ℤ` is
`genericPairConductor F ψ π (rankOneCharacter 1) hπ h₁`. Here `rankOneCharacter 1`
is the trivial character of `GL_1(F)`. Its genericity `h₁` is the published
`UniformRankOneTwist.isGeneric_rankOneCharacter_one`, restated privately for this
file's local instances. So `genericConductor` is `f(π × 1)`, which equals
`m - (r + 1) c(ψ)` for the epsilon factor `c q^(-ms)` of `π × 1`.

Each definition takes `ψ` as an explicit argument. The source asserts that
`f(π × σ)` does not depend on `ψ`; that assertion is the separate theorem
obligation described below.

## Proved properties

- `additiveConductor_eq_zero_of_hasIntegerConductor`: if `ψ` has conductor `𝔒`
  in Jacquet's sense (`Conductor.HasIntegerConductor`, from `Conductor/Essential`),
  then `c(ψ) = 0`. The proof shows that `ψ` is trivial on `𝔭^0 = 𝔒`. If `ψ` were
  trivial on `𝔭^(-1)`, then `ψ(ϖ⁻¹ y) = 1` for every integer `y`, where `ϖ` is the
  chosen uniformizer of the canonical data. The second clause of
  `HasIntegerConductor` would then put `ϖ⁻¹` in `𝔒`. That puts `1` in `𝔭^1`,
  contradicting `v(1) = 1 > exp(-1)`.
  `additiveConductor_eq_zero_iff_hasIntegerConductor` adds the published converse
  `HighlyRamified.hasIntegerConductor_of_additiveConductor_eq_zero`.
- `genericPairEpsilonCoefficientExponent_isPadic`: at every self-dual `ν`, the
  constructed data satisfy the full `IsPadicSymmetricEpsilonFactor F ψ ν π σ`
  relation. That relation includes the existence of a compatible quotient measure
  and of nonzero functionals, and the normalized functional equation for all of
  them and all unequal-rank blocks. The proof identifies `ν` with
  `localSelfDualHaar F ψ` by `Correspondence.eq_localSelfDualHaar` and uses
  `genericSymmetricEpsilonData_isPadic`.
- `genericPairEpsilonCoefficientExponent_eq` and `genericPairEpsilonExponent_eq`:
  every certified epsilon factor `e` at any self-dual `ν` equals the constructed
  data, so its exponent is `f(π × σ, ψ)`. The proof uses
  `IsPadicSymmetricEpsilonFactor.unique`.
  `genericPairEpsilonCoefficientExponent_eq_genericSymmetricEpsilonData` compares
  the data with the published constructor at any supplied self-dual measure.
- `genericPairConductor_eq`: for every certified `e` at a self-dual `ν`,
  `f(π × σ) = e.2 - (r + 1)(n + 1) c(ψ)`.
  `genericPairConductor_eq_epsilonExponent`: if `HasIntegerConductor ψ`, then
  `f(π × σ) = f(π × σ, ψ)`.
- `genericPairEpsilonCoefficientExponent_congr_equiv`,
  `genericPairConductor_congr_equiv` and `genericConductor_congr_equiv`: the data
  and both conductors are unchanged when `π` and `σ` are replaced by equivalent
  generic representations, which may have carriers in other universes. The proofs
  use `IsPadicSymmetricEpsilonFactor.congr_equiv` and uniqueness.
- `genericConductor_eq`: if `IsPadicPairEpsilonFactor F ψ ν π 1 (c, m)` holds at a
  self-dual `ν`, then `f(π) = m - (r + 1) c(ψ)`.
  `genericConductor_eq_of_hasIntegerConductor`: if moreover `ψ` has conductor `𝔒`,
  then `f(π) = m`. This is the JPSS 1981 convention, and the relation is the one
  that appears in `Conductor.ConductorExponentStatement`.
  `exists_isPadicPairEpsilonFactor_genericConductor` gives, at every self-dual `ν`,
  a coefficient `c` with
  `IsPadicPairEpsilonFactor F ψ ν π 1 (c, f(π) + (r + 1) c(ψ))`.

## Comparison with the published conductor statements

The last section takes two published, unproved statements as explicit
hypotheses. It shows that the constructed integers are the integers those
statements assert. These theorems do not prove the statements.

- `genericPairConductor_eq_of_pairEpsilonExponentStatement`: assume
  `RankinSelberg.PairEpsilonExponentStatement` (BHK 1998, printed p.703). Then for
  every two characters `ψ, ψ'` for which `π` and `σ` are generic,
  `genericPairConductor F ψ π σ … = genericPairConductor F ψ' π σ …`. The proof
  applies the statement at the measures `localSelfDualHaar F ψ` and
  `localSelfDualHaar F ψ'` to the constructed data.
- `genericConductor_isNewvectorConductor_of_conductorExponentStatement`: assume
  `Conductor.ConductorExponentStatement` (JPSS 1981, Théorème (5.1)) and that `ψ`
  has conductor `𝔒`. Then there is a natural number `m` with
  `genericConductor F ψ π hπ = m`, `IsNewvectorConductor π m` and
  `Module.finrank ℂ (levelFixedVectors π m) = 1`. The statement is instantiated at
  `F.Carrier` with these inputs:
  - the canonical instances, with Borel measurable structures on `F`,
    `GL_1(F)`, `N_1(F)` and `N_1\GL_1`;
  - `q = residueCardinality`;
  - the normalized absolute value;
  - the uniformizer and unit lemmas
    `HighlyRamified.exists_uniformizingElement_normalizedAbs` and
    `HighlyRamified.normalizedAbsoluteValue_eq_one`;
  - the measure `localSelfDualHaar F ψ`.

  The exponent it supplies is then identified by
  `genericConductor_eq_of_hasIntegerConductor`.

## Sources and correspondence

- Jacquet, Piatetski-Shapiro and Shalika, *Conducteur des représentations du
  groupe linéaire*, Math. Ann. 256 (1981), 199–214. Literature ID
  `jpss-1981-conductor`, SHA-256
  `986b06d6c16221fd55f04480604a1b17bf11004a704ab16b78acdd131ae6d49d`.
  - §(1.1), printed p.199 (PDF page 1): `ε(s, π, ψ) = ε_π(q^(-s), ψ)` with
    `ε_π(X, ψ) = c X^m`, under the standing hypothesis that the exponent of `ψ` is
    `0`, that is, the largest ideal on which `ψ` is trivial is `𝔒`. In that case
    `m` depends only on `π`.
  - §(5.1), printed p.211 (PDF page 13): for irreducible generic `π` and `ψ` of
    exponent `0`, `m` is the integer with `ε_π(X, ψ) = C X^m`. Théorème (5.1)
    gives `m ≥ 0`, that the essential vector is fixed by `K_r(m)` with a
    one-dimensional fixed space, and that no lower level has fixed vectors.
  - Remarque (5.4), printed p.214: the newvector interpretation fails for
    nongeneric representations. For that reason this module defines the conductor
    from the epsilon factor, not from fixed levels, and only for generic
    representations.
- Bushnell, Henniart and Kutzko, *Local Rankin–Selberg convolutions for GL_n:
  explicit conductor formula*, J. Amer. Math. Soc. 11 (1998), 703–730. Literature
  ID `bhk-1998-explicit-conductor`, SHA-256
  `5f3c996bc6be89966f3a39ecba68f58926137096bc8fce9b489f11be18167657`.
  - Introduction, printed p.703 (PDF page 1): the definition of `c(ψ)`,
    `ε(π₁ × π₂, s, ψ) = ε(π₁ × π₂, 0, ψ) q^(-f(π₁ × π₂, ψ) s)`, and
    `f(π₁ × π₂, ψ) = n₁ n₂ c(ψ) + f(π₁ × π₂)` with `f(π₁ × π₂)` independent of `ψ`.
  - Printed p.704 (PDF page 2): for the Godement–Jacquet conductor `f(π)`,
    `f(π) = f(π × 1_F)`, where `1_F` is the trivial representation of `GL_1(F)`.
- Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg convolutions*, Amer. J.
  Math. 105 (1983). Literature ID `jpss-1983-rankin-selberg`, SHA-256
  `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
  Theorem 2.7(iii), printed p.391, and §2.12, printed p.403, are the sources of the
  epsilon factors and of the larger-rank-first convention. These conventions are
  inherited unchanged from `PadicSymmetricEpsilonFactor`.

Provenance: the definitions transcribe BHK's `f(π × σ, ψ)` and `f(π × σ)` for the
constructed JPSS epsilon factors of generic pairs. The definition of `f(π)` as
`f(π × 1)` is derived. JPSS 1981 define the conductor of `π` through the
Godement–Jacquet factor `ε(s, π, ψ)`, and BHK p.704 record `f(π) = f(π × 1_F)`.
This module uses the JPSS pair factor against the trivial character of `GL_1`, the
same convention as `Conductor/EssentialStatement` (see the "Interpretation and
gaps" section of its Markdown). The Library has no Godement–Jacquet epsilon factor
for general `GL_n`, and the comparison `ε(s, π × 1, ψ) = ε(s, π, ψ)` is not proved.
Without it, `genericConductor` is the JPSS 1981 conductor with the JPSS pair factor
in place of the Godement–Jacquet factor.

## Scope and open obligations

- Only generic pairs are covered, because only for them does the Library construct
  the epsilon factor without hypotheses. BHK state the identity for all irreducible
  smooth pairs. Conductors of nongeneric representations would come from the
  Langlands-data epsilon factor `RankinSelberg.langlandsPairEpsilonFactorOfClassification`,
  which still takes classification inputs; they are not defined here.
- Not proved here:
  - independence of `ψ`, which is the content of
    `RankinSelberg.PairEpsilonExponentStatement`;
  - nonnegativity of `f(π)` and its newvector interpretation, which are
    `Conductor.ConductorExponentStatement`, with proof task
    `7b8711bf-90dc-40ae-923e-5bfecc3550b6`;
  - comparison with the Godement–Jacquet conductor;
  - BHK's bounds and explicit formulas.

  The two comparison theorems above only transfer the first two statements, when
  they are supplied as hypotheses, to the constructed integers.
- The rank-one comparison with Tate's conductor is the separate published
  reduction `Conductor/RankOneTateReduction`. It is not used here.

## Imports

- `RankinSelberg.PadicSymmetricEpsilonFactor`: the epsilon constructors and
  relations.
- `RankinSelberg.UniformRankOneTwistProof`: genericity of the trivial character of
  `GL_1`.
- `RankinSelberg.HighlyRamified.EssentialInput`: the converse conductor lemma and
  the normalization lemmas for the canonical data.
- `Correspondence.RankOneArithmeticEpsilonData`: the canonical self-dual measure.
- `LocalField.Normalization.Proof`: the valuation of the uniformizer.
- `Conductor.EssentialStatement` and `RankinSelberg.PairEpsilonNormalizationStatement`:
  the two statements used in the comparison section.

All imports are published Library modules. The module adds no axioms. The
inspected theorem `genericConductor_isNewvectorConductor_of_conductorExponentStatement`
uses only `propext`, `Classical.choice` and `Quot.sound`.
