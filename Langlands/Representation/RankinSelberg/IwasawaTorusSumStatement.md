# Discrete torus decomposition of the normalized Iwasawa pushforward

`Langlands.RankinSelberg.IwasawaTorusSumStatement.{uF}` is a closed
Prop-valued definition. It states an equality of actual measures on the left
unipotent quotient. This module supplies the statement only, with no proof.

The proposition quantifies every prime `p`, every `F : PadicField.{uF} p`,
every supplied `T : F.TopologicalData`, and every natural `n`. The rank is
`m = n+1`, including rank one. It installs `T.topology`, `T.valuativeRel`
and `T.localField`, then the Borel structures on field units, `GL_m(F)`,
the upper-unipotent subgroup and its left quotient, exactly as in
`QuotientIwasawaIntegrationStatement`. Diagonal coordinates and their
product with the group use the usual product measurable structures.
Every `ϖ : F.Carrierˣ` satisfying
`GeneralLinear.Iwasawa.IsUniformizingElement (ValuativeRel.valuation F.Carrier) ϖ`
is quantified. This predicate says that its valuation is below one and its
integer powers realize the valuation of every nonzero field element.

Write `A = Fin m → F.Carrierˣ`, `G = GL_m(F)`,
`Q = LeftUnipotentQuotient n F.Carrier`,
`O = (ValuativeRel.valuation F.Carrier).integer` and
`K = Conductor.integralSubgroup O n`. The local bindings are:

- `da = Measure.pi (fun _ => localMultiplicativeHaar F.Carrier)`.
- `dk = (generalLinearHaar F.Carrier n).restrict K`, a measure on the
  ambient group `G`, supported on `K`.
- `δ(a) = ∏_{i<j} T.normalizedAbs(a_i/a_j)`, using ordinary diagonal
  entries and the residue-cardinality normalized absolute value.
- `q(a,k) = [Iwasawa.diagonalUnits a * k]` in the actual left quotient.
- `t(λ)_i = ϖ ^ λ_i` for every `λ : Fin m → ℤ`.
- `qLam(λ)(k) = [Iwasawa.torus ϖ λ * k]`, using the published torus
  construction, which is definitionally `Iwasawa.diagonalUnits (t λ)`.

The exact equality is

```text
Measure.map q ((da.prod dk).withDensity
    (fun (a,k) => ENNReal.ofReal (δ(a)⁻¹))) =
  Measure.sum (fun λ : Fin m → ℤ =>
    ENNReal.ofReal (δ(t λ)⁻¹) • Measure.map (qLam λ) dk).
```

The sum ranges over every exponent vector, with no ordering or dominance
restriction. It is countable because `Fin m` is finite. Both sides are
measures with extended nonnegative values, so infinite integrals are allowed.
Once proved, the equality applies to all nonnegative measurable tests, not
only integrable or compactly supported functions. No convergence hypothesis,
complex integral, supplied quotient measure, compatibility condition,
unipotent Haar right-invariance instance or assumed Iwasawa measure formula
occurs in the proposition. The weight is the inverse upper-Borel modulus,
with scalar exactly one. For rank one the modulus is an empty product and
equals one.

This is an internal derived statement about existing Library constructions,
rather than a transcription of an external theorem. Its normalization comes
from `RankinSelberg.Measures`: `mem_integralUnits` identifies the integral
units, `localMultiplicativeHaar_integerUnits` gives them mass one, and
`generalLinearHaar_integralSubgroup` gives `K` mass one.
`Whittaker.Iwasawa` supplies the diagonal and torus maps,
`IsUniformizingElement`, and `diagonalUnits_mem`.
`LocalField.Normalization.Proof` supplies the normalized absolute-value
laws. The quotient and its topology are the existing constructions in
`RankinSelberg.QuotientIntegrals` and `Analysis.Local.QuotientTopology`.
All notation added here is local to the proposition.

The following argument describes the obligation for a future proof, rather
than a proof implemented in this module. Set `U = integralUnits O` and
`U_A = {u : A | ∀ i, u i ∈ U}`. Each diagonal vector decomposes uniquely as
`a = t(λ) * u`, with `λ : Fin m → ℤ` and `u ∈ U_A`. Existence follows
coordinatewise from the uniformizer predicate and valuation one of the
residual units. Uniqueness follows from strict monotonicity of powers of a
positive valuation below one. Thus the torus is the disjoint union of the
measurable cosets `t(λ) * U_A`. Each coset has product Haar mass one, by
multiplicative Haar invariance and the mass-one normalization of `U`.

Integral units have normalized absolute value one. The modulus is therefore
constant on each stratum, with value `δ(t λ)`. For `u ∈ U_A`,
`Iwasawa.diagonalUnits u ∈ K`, and
`q(t(λ) * u,k) = qLam(λ)(Iwasawa.diagonalUnits u * k)`.
Left translation by this integral diagonal matrix preserves `dk`: ambient
left Haar is invariant, and translation by an element of `K` preserves `K`.
This absorbs the integral-unit coordinate into the compact integration.
Its remaining integral has mass one, explaining the exact scalar.

A proof must establish the measurable partition, coordinate maps and density,
the restricted-Haar translation identity, and the nonnegative product and
countable-sum integration steps. These yield the asserted measure equality,
including infinite values. This argument is independent of the full quotient
Iwasawa integration formula and must not use that formula or a result that
assumes it to prove this prerequisite. In particular, the conditional
`quotientRootIntegration` theorem does not discharge this obligation.
The comparison with a compatible quotient measure and the actual quotient
orbit partition belong to the separate quotient Iwasawa proof.
