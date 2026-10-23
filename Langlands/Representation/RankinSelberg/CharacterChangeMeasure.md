# The character-change quotient Haar law from the subgroup modulus

Authors: Worker 235, with Markdown contributions by Worker 88.

The theorem `Langlands.RankinSelberg.characterChangeCompatibleMeasure` has
exactly the type
`Langlands.RankinSelberg.CharacterChangeCompatibleMeasureStatement.{uF}`.
It proves the published statement with no additional hypothesis.

The module first reduces the quotient law to the subgroup conjugation law
`Langlands.RankinSelberg.UnipotentCharacterChangeModulusStatement`. The
quotient part of this reduction is proved here in full, with the subgroup law
as an explicit hypothesis. The final theorem then discharges that hypothesis
with the published proof `Langlands.RankinSelberg.unipotentCharacterChangeModulus`
from `Langlands.Representation.RankinSelberg.UnipotentCharacterChangeModulusProof`.
No published file is modified.

This is an internal derivation from the published compatibility predicate,
quotient-measure uniqueness theorem, and character-change constructions.
It introduces no additional literature claim or measure normalization.

## Conventions and the direction of the two multipliers

Fix a nonarchimedean local field `F`, an absolute value `abv`, a natural
number `n`, and a unit `a`. Write

* `N = upperUnipotent (n + 1) F` for the upper-unipotent subgroup of
  `G = GL_(n+1)(F)`, and `N \ G = LeftUnipotentQuotient n F` for the left
  quotient;
* `d = characterChangeElement a n = diag(a^n, ..., a, 1)`;
* `C_a = characterChangeConj a n` for conjugation `u ↦ d u d⁻¹` on `N`;
* `T_a = characterChangeQuotient a n` for the quotient homeomorphism
  `N g ↦ N d g`;
* `c = characterChangeModulus abv a n = abv(a)^E`, where
  `E = characterChangeRootExponent n` is a natural number. The modulus
  `c : ℝ≥0` is nonzero; at `n = 0`, the exponent is zero and `c = 1`;
* `νG = generalLinearHaar F n` and `νN = unipotentHaar F n`;
* `A f (N g) = ∫_N f(u g) dνN(u)` for the published orbital average
  `quotientAverage N νN f` (`quotientAverage_mk`).

There are two pushforward laws with opposite multipliers.

* The **subgroup** law (the hypothesis `hN` below) has the
  **reciprocal** factor:
  `Measure.map C_a νN = c⁻¹ • νN`. Conjugation multiplies the `(i,j)`
  coordinate by `a^(j-i)`, so it scales volumes by `c`; a pushforward
  evaluates a set through its preimage, hence the factor `c⁻¹`.
* The **quotient** law `HasCharacterChangeMeasureLaw abv a μ`, which this
  module proves, has the **positive** factor:
  `Measure.map T_a μ = c • μ`.

All multipliers are coerced from `ℝ≥0` to `ℝ≥0∞`. Since `c ≠ 0`
(`characterChangeModulus_ne_zero`) and coerced values are finite, both
`c` and `c⁻¹` are finite and nonzero in `ℝ≥0∞`. The proofs use this
repeatedly.

## Declarations

### `characterChangeConjHomeomorph a n`

This packages `C_a` as a self-homeomorphism of `N`, with inverse
`C_(a⁻¹)`. The two inverse laws use `characterChangeConj_val`
(`C_a u = d u d⁻¹`) and `characterChangeElement_inv` (`d_a⁻¹ = d_(a⁻¹)`).
Both directions are continuous because they multiply the subgroup inclusion
by fixed matrices. The homeomorphism is needed as a measurable equivalence in
the change-of-variables formula `integral_map_equiv`.

### `rightTranslate_comp_characterChangeQuotient`

Left multiplication by `d` commutes with right translation, so on the
quotient `rightTranslate N g ∘ T_a = T_a ∘ rightTranslate N g`. The proof
uses `Quotient.inductionOn` and associativity.

### `quotientAverage_characterChangeQuotient` (orbital identity)

Assume `hN : Measure.map C_a νN = c⁻¹ • νN`. Then for every
`f : G → ℂ` and every `q ∈ N \ G`

```text
A f (T_a q) = c * A (x ↦ f (d x)) q .
```

For `q = N g`, the integrand on the right is `f(d u g)`. Since
`d u g = (d u d⁻¹)(d g) = C_a(u) (d g)`, it is
`v ↦ f(v (d g))` evaluated at `C_a(u)`. `integral_map_equiv` turns
`∫ f(C_a(u)(d g)) dνN(u)` into the integral of
`v ↦ f(v (d g))` against `Measure.map C_a νN`. By `hN` this measure is
`c⁻¹ • νN`, and `integral_smul_measure` gives
`(c⁻¹).toReal • A f (N d g)`. Hence `A(x ↦ f(d x))(N g) = c⁻¹ A f (N d g)`.
Multiplying by `c` gives the identity, because `c` is a nonzero real.
No integrability hypothesis on `f` is needed, because
`integral_map_equiv` and `integral_smul_measure` hold for arbitrary
integrands.

### `isCompatible_smul_map_characterChangeQuotient`

Assume `hN` and let `μ` be compatible, that is,
`IsCompatible N νG νN μ`. Then the measure

```text
ν = c⁻¹ • Measure.map T_a μ
```

is again compatible with the same Haar measures `νG` and `νN`. All five
fields of the published `QuotientIntegration.IsCompatible` are proved.

* `nonzero`: if `ν = 0`, multiply by `c`. Then `c * c⁻¹ = 1` gives
  `Measure.map T_a μ = 0`. Since `T_a` is measurable,
  `Measure.map_eq_zero_iff` gives `μ = 0`, contradicting the
  compatibility of `μ`.
* `regular`: `Measure.Regular.map` gives regularity of the pushforward along
  the homeomorphism `T_a`. `Measure.Regular.smul` preserves it under the
  finite scalar `c⁻¹`.
* `right_invariant`: for each `g`, the right translation `R_g` is
  measurable. Then `map R_g (c⁻¹ • map T_a μ) = c⁻¹ • map (R_g ∘ T_a) μ`.
  The commutation lemma turns this into `c⁻¹ • map T_a (map R_g μ)`.
  The right invariance of `μ` turns it back into `ν`.
* `averaging_integrable`: let `f` be continuous with compact support. Its
  left translate `f_d(x) = f(d x)` is also continuous with compact support
  (`HasCompactSupport.comp_homeomorph`). Integrability against a finite
  multiple of a measure is `Integrable.smul_measure`. Integrability against
  `map T_a μ` is integrability of `A f ∘ T_a` against `μ`
  (`integrable_map_equiv`). By the orbital identity, `A f ∘ T_a` is
  `c * A f_d`, and `A f_d` is integrable by the compatibility of `μ`.
* `integral_formula`: for `f` as above,

  ```text
  ∫ A f dν = c⁻¹ ∫ A f ∘ T_a dμ        (integral_smul_measure, integral_map_equiv)
           = c⁻¹ · c ∫ A f_d dμ        (orbital identity, integral_const_mul)
           = ∫ f(d x) dνG(x)           (Weil formula for μ applied to f_d)
           = ∫ f dνG                   (left invariance of νG,
                                        integral_mul_left_eq_self).
  ```

This is the step from compactly supported orbital averages to measures.
The orbital identity and left invariance of `νG` are needed only for
compactly supported continuous `f`. Those are exactly the test functions
in the compatibility predicate. No identity of measures is derived from them
directly. They only establish that `ν` satisfies the defining conditions.

### `hasCharacterChangeMeasureLaw_of_unipotentModulus`

Assume `hN` and let `μ` be compatible. The published uniqueness theorem
`unipotentQuotientHaar_unique F n` states that every measure compatible
with `νG` and `νN` equals `unipotentQuotientHaar F n`. Its proof in
`RankinSelberg/UnipotentQuotient` applies the Riesz-type uniqueness
theorem `measureOfPositiveAveraging_unique` from
`Analysis/Local/QuotientFunctional` to regular measures. First it applies the
complex Weil formula to real-valued test functions composed with
`Complex.ofReal`; `quotientAverage_ofReal`, `integral_complex_ofReal`, and
injectivity of `Complex.ofReal` recover the real Weil formula. Every compactly
supported continuous real function on the quotient is an orbital average,
and Mathlib's `Measure.ext_of_integral_eq_on_compactlySupported` then
determines the measure. The theorem applies to both `ν` and `μ`, so

```text
c⁻¹ • Measure.map T_a μ = unipotentQuotientHaar F n = μ .
```

Multiplying by `c` gives `Measure.map T_a μ = (c * c⁻¹) • map T_a μ = c • μ`.
`ENNReal.mul_inv_cancel` applies because `c` is nonzero and finite. This is
`HasCharacterChangeMeasureLaw abv a μ`, with the positive factor `c`.

The five declarations above hold for any field with the stated local-field
instances and Borel structures, and for an arbitrary absolute value `abv`.
They use only the hypothesis `hN` for that field, absolute value, `a` and
`n`.

### `characterChangeCompatibleMeasure_of_unipotentModulus`

This theorem takes `UnipotentCharacterChangeModulusStatement` as a
hypothesis and proves `CharacterChangeCompatibleMeasureStatement`. For
each prime `p`, `F : PadicField p`, actual `T : F.TopologicalData`, `n`
and `a`, it installs the instances of the target statement. They are the
topology, valuative relation and local-field instance from `T`, and the
Borel structures on `G`, `N` and `N \ G`. These are the same instance
terms that the subgroup statement uses for `N`. The theorem then applies
`hasCharacterChangeMeasureLaw_of_unipotentModulus` with
`abv = normalizedAbsoluteValue T` and the subgroup law for the same data.

### `characterChangeCompatibleMeasure`

This is the target theorem:

```text
theorem characterChangeCompatibleMeasure :
    CharacterChangeCompatibleMeasureStatement.{uF}
```

It applies `characterChangeCompatibleMeasure_of_unipotentModulus` to the
published proof `unipotentCharacterChangeModulus :
UnipotentCharacterChangeModulusStatement.{uF}`. Both statements quantify over
the same field-carrier universe `uF`, so the universe levels match.

Concretely, for every prime `p`, `F : PadicField p`, actual
`T : F.TopologicalData`, natural number `n`, unit `a : F.Carrierˣ` and
measure `μ` on `N \ G` that is compatible with `generalLinearHaar F.Carrier n`
and `unipotentHaar F.Carrier n` (with the topology, valuative relation,
local-field instance and Borel structures that the statement installs from
`T`), `HasCharacterChangeMeasureLaw (normalizedAbsoluteValue T) a μ` holds,
that is,

```text
Measure.map (characterChangeQuotient a n) μ
  = (characterChangeModulus (normalizedAbsoluteValue T) a n : ℝ≥0∞) • μ .
```

The proof uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.
