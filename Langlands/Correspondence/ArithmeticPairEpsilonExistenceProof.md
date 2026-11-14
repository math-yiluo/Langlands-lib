# Existence of arithmetic pair epsilon factors (proof)

Author: Worker 391.

This module proves the published proposition
`Langlands.Correspondence.ArithmeticPairEpsilonExistenceStatement.{u, uV, uE}`
(module `Langlands.Correspondence.ArithmeticPairEpsilonExistenceStatement`). The main
theorem is

```
theorem Langlands.Correspondence.arithmeticPairEpsilonExistence :
    ArithmeticPairEpsilonExistenceStatement.{u, uV, uE}
```

It has no extra hypothesis. Its axioms are `propext`, `Classical.choice` and `Quot.sound`.

The statement says the following. Fix a `p`-adic field `K`, a common-closure
local-constant system `ε` for `eC` (`IsSystem K eC ε`), a nontrivial additive character
`ψ`, and Weil–Deligne pair classes `X`, `Y` whose representatives have continuous
underlying Weil representations. Then there are `c : ℂˣ` and `m : ℤ` with
`IsArithmeticPairEpsilonFactor K eC ε hε ψ X Y c m`. This predicate has three parts:

1. an admissible bottom-field datum `(ψ', μ, A, B)` with continuous `A`, `B` exists;
2. a geometric Frobenius over the bottom field exists;
3. at every admissible datum, every Frobenius `Φ` and every `s`, the conditional pair
   epsilon value equals `c · (q^(-s))^m`.

Mathematically, the proof is Tate's formula (3.4.5): `ε(V ω_s) = ε(V) q^(-(a(V) + n(ψ) dim V) s)`
(Tate 1979, printed p. 15; Deligne 1973, (5.5.2)). The Weil–Deligne correction
(Tate 1979, (4.1.6)) is already a monomial in `q^(-s)` by definition. The Library already
has the conditional Deligne value and its Weil–Deligne correction. This module adds two
things: the exponent in (3.4.5) is an integer, and the value does not depend on the
admissible datum.

Throughout, `K : PadicField.{u} p`, `qK` is the residue cardinality of `K` as a natural
number, and `baseCardinality K` is the same number as a real. Pairs over the bottom field
are `CommonClosureWeilDeligne.Pair.{u, uE} K (baseExtension K)`.

## Part 1: moving the carrier (namespace `Langlands.WeilDeligneRepresentation`)

- `transportCarrier A e`: for a Weil–Deligne representation `A` over `ℂ` and a linear
  isomorphism `e : A ≃ₗ[ℂ] W`, this is the representation on `W`. Its action is
  `g ↦ e ∘ A(g) ∘ e⁻¹` (via `LinearEquiv.conjAlgEquiv`) and its monodromy is
  `e ∘ N ∘ e⁻¹`. Nilpotence and the covariance `ρ(g) N ρ(g)⁻¹ = ν(g) N` are transported
  through the algebra isomorphism.
- `transportCarrierEquiv A e`: `e` is an equivalence of Weil–Deligne representations from
  `A` to `transportCarrier A e`.

## Part 2: the bottom-field datum (namespace `Langlands.Correspondence.ArithmeticPairEpsilonExistence`)

- `basePair K B`: for a local pair `B : LocalWeilDeligneRepresentation.{u, uV} K`, this
  restricts `B` to `weilSubgroup K (baseExtension K)` (`WeilDeligneRepresentation.restrict`
  along the subtype). The carrier is then moved to `ULift.{max u uE} (Fin n → ℂ)`, where
  `n = finrank B`, using the basis `Module.finBasis` and `ULift.moduleEquiv`. This puts the
  pair in the carrier universe `max u uE` of common-closure pairs, which is required
  because `uV` and `uE` are independent.
- `basePairEquiv K B`: the restriction is equivalent to `basePair K B`.
- `basePair_isBaseRestriction`: `basePair K B` satisfies
  `IsBaseRestriction K (classOf B)`, with witness `B` and `basePairEquiv`.
- `basePair_isContinuous`: if `B` is continuous, so is `basePair K B`. Restriction along
  the continuous inclusion preserves continuity (`FiniteRepresentation.isContinuous_restrict`),
  and continuity is invariant under equivalence (`isContinuous_iff_of_equiv`).

The main theorem's datum uses these pairs together with three Library objects:

- the transported character `baseFieldAdditiveCharacterEquiv K ψ`
  (`RankOneEpsilonFieldTransport`);
- the transported self-dual measure `baseFieldHaarMeasureEquiv K (localSelfDualHaar K ψ)`,
  which is self-dual by `isSelfDual_baseFieldTransport_iff` and
  `isSelfDual_localSelfDualHaar`;
- the geometric Frobenius `baseGeometricFrobenius K` (`BaseLocalEuler`).

## Part 3: Tate (3.4.5) with an integral exponent

- `virtualTwist_eq_of_spectralParameter_eq`: the spectral twist `virtualTwist K E s`
  depends on `s` only through `spectralParameter q s`, that is, through `q^(-s)`. This
  holds because `SpectralTwist.character` is the unramified character given by that
  parameter. The proof unfolds the definitions and rewrites.
- `exists_int_of_cpow_period`: if `q > 1` and `q^(-r · 2πi / log q) = 1`, then
  `r ∈ ℤ`. This follows from `Complex.exp_eq_one_iff`.
- `one_lt_baseCardinality`: `1 < q`.
- `conditionalDeligneValue_monomial`: let `A` be a continuous representation of the
  bottom Weil group (over `ConductorExponent.base K`, as in the Library statement). Then
  there is `k : ℤ` with `D(s) = D(0) · (q^(-s))^k` for all `s`, where `D(s)` is the
  conditional Deligne value of `baseClass A` at `s`. The proof:
  1. `ConductorExponent.SpectralConductorStatement` is obtained from the Library reduction
     `SpectralConductor.spectralConductorRankOneReduction`. Its two premises are the proved
     `Ramification.Padic.finiteInertiaConductorRefinement` and
     `SpectralConductor.commonClosureRankOneConductor`. No unproved proposition is used.
  2. The restriction of `A` along `ConductorExponent.baseInclusion` is continuous. So a
     finite-inertia presentation `P` exists
     (`HerbrandBridge.continuousWeilFiniteInertiaPresentation`), and its restriction map
     is surjective (`HerbrandBridge.weilInertiaRestriction_surjective`). The statement then
     gives `D(s) = D(0) · q^(-r s)` with `r = a(P) + n(ψ) · rank A`.
  3. Periodicity. Set `t = 2πi / log q`. Then `spectralParameter q t = spectralParameter q 0`,
     so `D(t) = D(0)` by the previous lemma. `D(0)` is a unit, hence nonzero, so
     cancelling it gives `q^(-r t) = 1`, and therefore `r = k ∈ ℤ`.
  4. Finally `q^(-k s) = (q^(-s))^k` by `Complex.cpow_int_mul`, which is the claimed shape.

## Part 4: the Weil–Deligne correction and the full value

- `quotientValue_monomial`: over the bottom field, the quotient correction factor is
  `quotientValue(s) = quotientValue(0) · (q^(-s))^d`, where `d` is the conductor
  correction `WeilDeligne.conductorCorrection C (inertia K (baseExtension K))`. By
  definition the factor is `quotientConstantCorrection · spectralParameter(q_E, s)^d`, and
  `spectralParameter_eq_cpow` and `baseResidueCardinality_real` identify
  `spectralParameter(q_E, s)` with `q^(-s)`.
- `conditionalEpsilonValue_monomial`: let `C` be a continuous pair over the bottom field
  and `Φ` a Frobenius. Then the conditional epsilon value satisfies
  `ε(s) = ε(0) · (q^(-s))^(k + d)`. The conditional epsilon value is the Deligne value of
  `underlyingClass C` times the quotient value. `underlyingClass C` is definitionally
  `baseClass` of the underlying representation, so Part 3 applies.

## Part 5: the main theorem

Let `B₁`, `B₂` be the continuous representatives of `X` and `Y`. Set
`ψ₀ = baseFieldAdditiveCharacterEquiv K ψ`, `μ₀` the transported self-dual measure, and
`Aᵢ = basePair K Bᵢ`. Apply `conditionalEpsilonValue_monomial` to the tensor `A₁ ⊗ A₂`
(continuous by `CommonClosureGamma.tensor_isContinuous`) with Frobenius
`baseGeometricFrobenius K`. This gives `m`. Take `c` to be the conditional pair epsilon
value of this datum at `s = 0`.

- **Existence.** The datum `(ψ₀, μ₀, A₁, A₂)` is admissible by Parts 1 and 2, and
  `baseGeometricFrobenius K` is a Frobenius.
- **Independence.** Let `(ψ', μ, A, B)` be any admissible continuous datum and `Φ` any
  Frobenius.
  - `ψ' = ψ₀` by `isBaseCharacter_iff_eq_baseFieldAdditiveCharacterEquiv`.
  - `μ = μ₀`: transport `μ` back to `K`. It is self-dual there
    (`isSelfDual_of_isBaseCharacter_iff`), so it equals `localSelfDualHaar K ψ`
    (`eq_localSelfDualHaar`).
  - `A ≃ A₁` and `B ≃ A₂`, because two base restrictions of one class are equivalent
    (`IsBaseRestriction.nonempty_equiv`, composed with `basePairEquiv`). The pair value is
    invariant under such equivalences
    (`CommonClosureGamma.conditionalPairEpsilonValue_eq_of_equiv`).
  - Changing `Φ` to `baseGeometricFrobenius K` does not change the value
    (`conditionalEpsilonValue_eq_of_frobenius`).

  Then the monomial formula above gives the value `c · (q^(-s))^m`, which is
  `RankinSelberg.epsilonMonomial qK c m s` by definition.

## Sources

- J. Tate, *Number theoretic background* (1979), `tate-1979-number-theoretic-background`:
  (3.4.5), printed p. 15, and (4.1.6), printed pp. 20–21.
- P. Deligne, *Les constantes des équations fonctionnelles des fonctions L* (1973),
  `deligne-1973-local-constants`: (5.5.2) and §8.

The integrality of the exponent and the independence of the datum are not taken from
these sources. They are proved here from the Library definitions, by the periodicity and
uniqueness arguments above.
