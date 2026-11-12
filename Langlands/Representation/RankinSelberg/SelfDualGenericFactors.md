# Generic p-adic pair factors at the actual self-dual Haar measure

Author: Worker 18 (task `6f0365a3-7419-4804-b209-3fc348b878de`).

This module gives the local factors of generic pairs as functions of the
additive character `ψ` and the pair alone:

- the epsilon factor `ε(s, π × σ, ψ)`, as a rational-function unit and as a
  complex value;
- the L-polynomial and L-factor `L(s, π × σ)`;
- the L-polynomial and L-factor of the inverse-transpose pair, the dual factor
  that enters the functional equation;
- the gamma factor `γ(s, π × σ, ψ)`, with its regular spectral domain and its
  complex value.

The Library already constructs all of these. Its constructors
(`genericSymmetricEpsilonFactor`, `genericSymmetricLFactor`,
`genericSymmetricDualLFactor`, `genericSymmetricGammaFactor`) take an additive
Haar measure `ν` and, for epsilon and gamma, a proof of `IsSelfDual ψ ν`. In the
sources the measure is not a parameter: it is the Haar measure that is self-dual
for `ψ`. The Library proves that this measure exists and is unique, and selects
it as `Correspondence.localSelfDualHaar F ψ`. This module evaluates the
published constructors at that measure. It proves that the results agree with
the published constructors, and satisfy their full relations, at every
self-dual `ν`. No new measure, existence hypothesis or default value is
introduced.

## Setting and normalization

- **Field.** `F : PadicField p`, for any prime `p` and field universe `uF`, with
  the canonical structure. The topology is that of `F.canonicalNormedField`; the
  valuation and local-field structure are those of
  `F.canonicalTopologicalData`; the measurable structure is Borel. These are the
  local instances of `RankinSelberg/PadicGenericGammaExpression`, whose
  constructors are reused. The private `valuative_nonarchimedean` proof is copied
  from that module. It derives the nonarchimedean additive structure from the
  open-submodule basis and adds no assumption.
- **Spectral variable.** `q` is `F.canonicalTopologicalData.residueCardinality`.
  Rational functions are in `X = q^(-s)`; `spectralPoint q s = q^(-s)`. An epsilon
  factor `(c, m)` is the monomial `c X^m`, with value `c q^(-ms)`. An L-factor is
  `P(X)⁻¹` with `P(0) = 1`.
- **Representations.** `π` acts on a complex module `V` (universe `uV`) through
  `GL_(r+1)(F)`, and `σ` on `W` (universe `uW`) through `GL_(n+1)(F)`. All
  positive ranks are allowed, including rank one and unequal ranks, in either
  order. Both are `Whittaker.IsGeneric` for `ψ`: irreducible, admissible, and
  with a nonzero standard Whittaker functional. As in the published
  constructors, the pair is read with the larger rank first (JPSS §2.12); at
  equal ranks the given order is kept.
- **Additive character and measure.** `ψ` is any `UnitaryAdditiveCharacter`
  (continuous, nontrivial, unit-circle valued). The measure is
  `Correspondence.localSelfDualHaar F ψ`, the Haar measure self-dual for `ψ`
  under the plus-sign Fourier transform. It is chosen only from the proved
  `Correspondence.existsUnique_localSelfDualMeasure`, and
  `Correspondence.eq_localSelfDualHaar` identifies it with every `ν` satisfying
  `IsSelfDual ψ ν`.
- **Dual pair.** The dual factor is the published one: the L-factor of the
  inverse-transpose pair `g ↦ π(ᵗg⁻¹)`, `g ↦ σ(ᵗg⁻¹)` for the character
  `ψ.scale (-1) = ψ⁻¹`, at the same measure. This is the JPSS model of the
  contragredient pair in the functional equation. The identification of
  `π(ᵗg⁻¹)` with the smooth contragredient of `π` is not used or proved here.

## Definitions

Each definition takes `F`, `ψ`, `π`, `σ` and the two genericity proofs.

- `selfDualGenericEpsilonFactor : RationalFunctionsˣ` is
  `genericSymmetricEpsilonFactor` at `localSelfDualHaar F ψ`.
- `selfDualGenericEpsilonValue (s : ℂ) : ℂˣ` is `genericSymmetricEpsilonValue`
  there: the nonzero number `c q^(-ms)`.
- `selfDualGenericLPolynomial : ℂ[X]` and `selfDualGenericLFactor :
  RationalFunctionsˣ` are `genericSymmetricLPolynomial` and
  `genericSymmetricLFactor` there.
- `selfDualGenericDualLPolynomial` and `selfDualGenericDualLFactor` are
  `genericSymmetricDualLPolynomial` and `genericSymmetricDualLFactor` there.
- `selfDualGenericGammaFactor : RationalFunctionsˣ` is
  `genericSymmetricGammaFactor` there.
- `selfDualGenericGammaRegularDomain : Set ℂ` is the set of `s` at which the
  reduced denominator of the gamma factor does not vanish at `q^(-s)`, and
  `selfDualGenericGammaValue` evaluates the gamma factor at `q^(-s)` on that set.
  Both are the published `genericSymmetricGammaRegularDomain` and
  `genericSymmetricGammaValue` at the self-dual measure.

## Proved properties

In every statement below, `ν` is any additive Haar measure with
`hν : IsSelfDual ψ ν`. Each proof first replaces `ν` by
`localSelfDualHaar F ψ` using `Correspondence.eq_localSelfDualHaar`.

- **Agreement with the published constructors.**
  `selfDualGenericEpsilonFactor_eq_genericSymmetricEpsilonFactor`,
  `selfDualGenericEpsilonValue_eq_genericSymmetricEpsilonValue`,
  `selfDualGenericLPolynomial_eq_genericSymmetricLPolynomial`,
  `selfDualGenericLFactor_eq_genericSymmetricLFactor`,
  `selfDualGenericDualLPolynomial_eq_genericSymmetricDualLPolynomial` and
  `selfDualGenericGammaFactor_eq_genericSymmetricGammaFactor`: each new object
  equals the published constructor at `ν`.
- **Epsilon.** `selfDualGenericEpsilonFactor_eq`: if
  `IsPadicSymmetricEpsilonFactor F ψ ν π σ e`, the factor is
  `rationalEpsilonMonomial e.1 e.2`. `selfDualGenericEpsilonValue_eq`: then the
  value at `s` is `epsilonMonomial q e.1 e.2 s`.
  `exists_isPadicSymmetricEpsilonFactor_selfDualGenericEpsilonFactor`: such a
  certified `e` exists at every self-dual `ν`. The certificate is the full
  relation of `PadicPairFactors`: compatible quotient measure, nonzero
  functionals and the normalized functional equation for every unequal-rank
  block.
- **L-factors.** `selfDualGenericLPolynomial_isPadic`: the polynomial satisfies
  `IsPadicSymmetricLPolynomial F ψ ν π σ`. `selfDualGenericLPolynomial_eq`: it is
  the only polynomial that does. `selfDualGenericLPolynomial_coeff_zero`: its
  constant coefficient is `1`. `coe_selfDualGenericLFactor`: the factor is the
  reciprocal of the polynomial.
- **Dual L-factors.** `selfDualGenericDualLPolynomial_isPadic` and
  `selfDualGenericDualLPolynomial_eq`: the polynomial satisfies, and is the unique
  solution of, `IsPadicSymmetricLPolynomial F (ψ.scale (-1)) ν` for the
  inverse-transpose pair. Its constant coefficient is `1`, and the factor is its
  reciprocal (`coe_selfDualGenericDualLFactor`).
- **Gamma.** `selfDualGenericGammaFactor_isPadic`,
  `selfDualGenericGammaFactor_eq` and
  `isPadicSymmetricGammaFactor_iff_eq_selfDualGenericGammaFactor`: the factor
  satisfies `IsPadicSymmetricGammaFactor F ψ ν π σ`, and a rational function
  satisfies that relation exactly when it is this factor.
  `selfDualGenericGammaFactor_eq_mul`: the gamma unit is

  `selfDualGenericEpsilonFactor * reflect(selfDualGenericDualLFactor) /
  selfDualGenericLFactor`,

  where `reflect` is `RationalReflection.subst` at
  `LocalFactor.residueReflection F`, the substitution `X ↦ q⁻¹ X⁻¹` that takes
  `q^(-s)` to `q^(-(1-s))`. This is `γ(s) = ε(s) L^∨(1 - s) / L(s)`, transferred
  from `genericSymmetricGammaFactor_eq_unit`.
- **Spectral values.** `selfDualGenericGammaValue_eq` restates the value as the
  evaluation of the gamma factor at `q^(-s)`.
  `mem_selfDualGenericGammaRegularDomain_of_dualPolynomial`: if the dual
  polynomial does not vanish at `q^(-(1-s))`, then `s` is in the regular domain.
  `selfDualGenericGammaValue_eq_localFactors`: for such `s`,

  `γ(s) = ε(s) P(q^(-s)) / P^∨(q^(-(1-s)))`,

  with `P` the L-polynomial and `P^∨` the dual L-polynomial.
- **Equivalence invariance.** `selfDualGenericEpsilonFactor_congr_equiv`,
  `selfDualGenericEpsilonValue_congr_equiv`,
  `selfDualGenericLPolynomial_congr_equiv`, `selfDualGenericLFactor_congr_equiv`
  and `selfDualGenericGammaFactor_congr_equiv`: the objects do not change when `π`
  and `σ` are replaced by equivalent generic representations, whose carriers may
  lie in other universes. The proofs use the published `congr_equiv` lemmas for
  the three relations and uniqueness.

## Sources and correspondence

- Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg convolutions*, Amer. J.
  Math. 105 (1983), 367–464. Literature ID `jpss-1983-rankin-selberg`, SHA-256
  `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
  - Printed p.378 (PDF page 13): the Fourier transform on Schwartz–Bruhat
    functions is taken with "the Haar-measure `dy` being self-invariant", that is,
    self-dual for `ψ`. This is why the factors here are evaluated at the
    self-dual measure.
  - Theorem 2.7, printed pp.390–391: the L-factor as normalized generator, the
    epsilon factor `ε(s, π × σ, ψ)` and the functional equation with the dual
    pair. Section 2.12, printed p.403: the larger-rank-first convention. These
    conventions are inherited unchanged from the published constructors.
- Henniart, *Une caractérisation de la correspondance de Langlands locale pour
  GL(n)*, Bull. Soc. Math. France 130 (2002), 587–602. Literature ID
  `henniart-2002-characterization`, SHA-256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
  §1.2, printed pp.588–589: the factors `L(s, π × π')` and `ε(s, π × π', ψ)` of
  JPSS are indexed by `ψ` and the pair only; L-factors have the form `P(q^(-s))⁻¹`
  with `P(0) = 1`, epsilon factors the form `α q^(-ms)`; and
  `γ = ε L(1 - s, ∨) / L(s)`. The following Remarque says that the factors depend
  only on the isomorphism classes. The equivalence-invariance theorems above
  prove that for generic pairs.
- Henniart, *Caractérisation de la correspondance de Langlands locale par les
  facteurs ε de paires*, Invent. Math. 113 (1993), 339–350. Literature ID
  `henniart-1993-epsilon-pairs`, SHA-256
  `057967169237036da64c0e5a72c69e8ddfd69176bebade0ef13588de24809763`.
  §1.1, printed pp.339–340: for the epsilon and gamma factors, the Haar measure
  on `F` self-dual for `ψ` is implicit in JPSS and does not appear in the
  notation. §2.3, printed p.343: (2.3.1) the Whittaker function
  `W̃(g) = W(w ᵗg⁻¹)` of the contragredient for `ψ⁻¹`, the inverse-transpose
  model used for the dual factor here; (2.3.4) the gamma factor
  `γ = ε L(π^∨ × τ^∨, 1 - s) / L(π × τ, s)`.

Provenance: derived. The objects are the published JPSS constructors evaluated
at the Library's unique self-dual measure. This removes the measure parameter,
as in the sources. The L-polynomial relations accept any additive Haar measure.
Here they are evaluated at the same self-dual measure as epsilon and gamma, which
is the measure the gamma relation and `genericSymmetricGammaFactor_eq_unit` use.

## Scope and open obligations

- Only generic pairs are covered, as in the published constructors. Nongeneric
  factors come from the Langlands-data constructors in
  `RankinSelberg/LanglandsFactors` and `LanglandsFactorDescent`, which take
  classification inputs.
- Not proved here:
  - independence of the L-polynomial from the additive Haar measure;
  - the identification of the inverse-transpose pair with the contragredient
    pair;
  - character-change, twist, rank-exchange and multiplicativity laws.

  These are separate statement and proof responsibilities. Character-change
  and twist interfaces for the measure-parameterized relations are already in
  `RankinSelberg/CharacterChange`, `CanonicalCharacterChange` and `Twist`.
- The epsilon coefficient and exponent, and the conductors read off from them,
  are defined in `Conductor/GenericEpsilonConductor` (accepted candidate
  `50036023-c9df-4e7d-a492-16054c7c398f`, awaiting integration when this was
  written), at the same measure. This module does not import it.

## Imports

- `RankinSelberg.PadicGenericGammaExpression`: the generic epsilon, L, dual L and
  gamma constructors and the gamma assembly.
- `Correspondence.RankOneArithmeticEpsilonData`: the self-dual measure
  `localSelfDualHaar`, its self-duality and its uniqueness.

Both are published Library modules. The module adds no axioms. The inspected
theorem `selfDualGenericGammaValue_eq_localFactors` uses only `propext`,
`Classical.choice` and `Quot.sound`.
