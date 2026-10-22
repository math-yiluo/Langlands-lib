# Supplied common-closure systems on standalone inputs

Worker 40 authored this derived attachment in the namespace
`Langlands.LocalFactor.CommonClosureSystemTransport`. It evaluates one
component of an explicitly supplied common-closure local-constant system on
actual standalone harmonic and Weil inputs. It also constructs the conditional
standalone Weil–Deligne epsilon value and proves its compatibility with the
published common-closure value.

## Actual field and harmonic inputs

Fix a prime `p`, independently universe-polymorphic finite p-adic fields
`F : PadicField.{uF} p` and `E : PadicField.{uE} p`, and an actual
algebra homomorphism `f : F.Carrier →ₐ[Padic p] E.Carrier`. Write

- `J = LocalClassField.extensionFiniteIntermediate F E f` for the finite
  image field in the specified algebraic closure of `F`;
- `a = extensionIntermediatePadicEquiv F E f` for the actual algebra
  equivalence from `E` to `J`;
- `w = extensionImageWeilEquiv F E f` for the actual topological
  equivalence from the standalone Weil group `W_E` to the fixing subgroup
  `W_J` inside `W_F`;
- `T = CommonClosureSpectral.Transport.virtualEquiv F E f` for the
  induced integer-linear equivalence of continuous exact virtual groups.

These are imported constructions. No comparison map, equality of residue
cardinalities, or character compatibility is a new hypothesis.

All field topologies are canonical, and all measurable spaces are their
Borel spaces. The local algebra instance on `J` is the one belonging to
`J.asPadicField`; specifying it keeps the existing algebra equivalence
and canonical field-data constructions aligned.

`imageAdditiveCharacter F E f ψ` specializes the published
`PadicField.ConductorTransport.additiveCharacter`. Its input is an actual
continuous nontrivial unitary additive character on `E`; its value at
`y : J.field` is `ψ (a.symm y)`. The imported construction supplies the
additive, continuous, unitary, and nontrivial properties. The theorem
`imageAdditiveCharacter_apply` exposes this formula by reflexivity.

`imageHaarMeasure F E f μ` specializes the published
`PadicField.AbelianTransport.haarMeasure`. It pushes the actual regular
additive Haar measure forward along `a`. The theorem
`imageHaarMeasure_measure` identifies the underlying measure with
`MeasureTheory.Measure.map a μ.measure`, again by reflexivity. In
particular the constructor does not introduce a separately supplied
normalizing scalar or choose a new Haar measure.

## Conditional ordinary values

Let `e : CommonClosure.ReciprocityFamily F`,
`ε : NonabelianSystem.Assignment.{uF,uV} F`, and
`hε : NonabelianSystem.IsSystem F e ε` be explicitly supplied. The last
hypothesis includes the full normalized reciprocity condition and the
existing additivity, Haar scaling, degree-zero induction, and rank-one
laws. The construction selects neither `e` nor `ε` and proves no
existence assertion.

Write `Tw_E(s)` for `SpectralTwist.virtual (localDegree E) q_E hq_E s`,
where `q_E` is the actual residue cardinality. This is the twist by the
continuous character with value
`exp(-s * Real.log q_E) ^ d_E(g)` at a Weil element `g`; the real
logarithm is cast into the complex numbers. Write `Tw_F,J(s)` for the
common-closure twist, which uses the ambient base-field cardinality and
degree. The published arithmetic comparison proves
`T (Tw_F,J(s) x) = Tw_E(s) (T x)`.

`virtualEquiv_symm_twist` derives its inverse form

\[
 T^{-1}(\operatorname{Tw}_E(s)x)
 =\operatorname{Tw}_{F,J}(s)(T^{-1}x).
\]

The proof applies the injective map `T`, then uses the published forward
identity and the inverse laws of the linear equivalence.

For `x : StandaloneVirtual.{uE, max uF uV} E`, the new
`conditionalDeligneValue F E f e ε hε ψ μ x s` is exactly

\[
 \varepsilon\bigl(J,\psi\circ a^{-1},a_*\mu,
                 T^{-1}(\operatorname{Tw}_E(s)x)\bigr).
\]

It is a complex unit because the explicitly supplied assignment is
unit-valued. Its definition takes the full system hypothesis, although
this hypothesis is not used to compute the expression.

`conditionalDeligneValue_eq` uses the inverse twist identity to identify
this value with the published
`CommonClosureSpectral.conditionalDeligneValue` at the transported
harmonic inputs and class `T.symm x`. The theorem
`conditionalDeligneValue_virtualEquiv` specializes this comparison to
`x = T y` for every common-closure class `y`. Both keep the complex
spectral coordinate `s` unchanged.

`conditionalDeligneValue_add` uses linearity of both virtual maps and
the supplied system's additivity law to turn an exact virtual sum into
a product of values. `conditionalDeligneValue_zero` uses preservation
of zero and the published `NonabelianSystem.value_zero`. The latter is
normalization at the zero virtual class for every `s`, not a claim
about setting the spectral coordinate to zero.

The exact virtual groups are the existing quotients by genuine short
exact relations on isomorphism classes of finite-dimensional continuous
complex representations. They are not quotients by direct sums alone.
The vector-space universe on both sides of `T` is `max uF uV`, while
the standalone group universe is `uE`. Continuity uses the existing
usual endomorphism-topology predicate; no alternative representation
category is identified with it here.

## Conditional Weil–Deligne values

`standaloneUnderlyingClass E A hA` inserts the ordinary underlying
representation of an actual standalone Weil–Deligne pair into the
continuous exact quotient. Its own carrier universe `uV` is independent
of `uE`; use in the transported system specializes it to `max uF uV`.
The continuity certificate `hA` is explicit. The theorem
`standaloneUnderlyingClass_eq_of_equiv` uses the exact quotient's
invariance under the ordinary representation equivalence underlying a
pair equivalence.

`underlyingClass_standalonePair` proves

\[
 T([\operatorname{underlying}(A)])
   =[\operatorname{underlying}(\operatorname{standalonePair}(A))].
\]

It specializes the published generator formula for `T`. The underlying
representation of `standalonePair` is definitionally restriction along
`w`; its published continuity proof is the same restriction certificate.
This supplies compatibility of the actual classes without a new quotient
or a supplied compatibility relation.

For any standalone pair `A` with carrier universe `max uF uV`, continuous
underlying representation, and a supplied degree-one element
`Φ : {g : W_E // localDegree E g = Multiplicative.ofAdd (1 : ℤ)}`,
`conditionalEpsilonValue` is

\[
 \operatorname{conditionalDeligneValue}([\operatorname{underlying}(A)],s)
 \;\det\!\left(-q_E^{-s}r_A(\Phi)
       \mid V_A^{I_E}/(\ker N_A)^{I_E}\right).
\]

The second factor is exactly
`WeilDeligne.quotientCorrectionValue A (localInertia E) Φ.val`
at the unit `spectralParameter q_E hq_E s`. The invariant quotient,
induced operator, and nonvanishing determinant come from the imported
construction. The covariance character of `A` is the actual
`localNormCharacter E`, and degree one has norm `q_E^(-1)`.
No Frobenius lift is selected by this module.

`conditionalEpsilonValue_eq_of_equiv` combines equality of the ordinary
exact classes with the existing invariance of the quotient correction
polynomial under pair equivalence. The determinant step uses unit
extensionality and the polynomial evaluation formula.

Finally, `conditionalEpsilonValue_standalonePair` identifies the full
standalone value of a common-closure pair's `standalonePair` with
`CommonClosureWeilDeligne.conditionalEpsilonValue` at the image-field
harmonic inputs and `geometricFrobeniusEquiv F E f Φ`. Its proof rewrites
the underlying class, uses the ordinary comparison, and uses the
published `quotientValue_standalonePair`. Thus it retains the actual
monodromy quotient correction as well as the ordinary factor.

## Provenance and scope

The conventions are inherited from Tate, *Number theoretic background*
(1979), §3.6, printed page 17 / retained Part II PDF page 26, and
§4.1.6, printed page 21 / PDF page 30. The former distinguishes
Deligne's measure-dependent constant from Langlands' half-twisted
self-dual convention. The latter gives the determinant correction on
`V^I/(ker N)^I`. These original pages were read directly for this unit.
Registered source: `tate-1979-number-theoretic-background`; exact PDF
SHA-256:
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.

The transport and its identities are internal derived content, using
the published harmonic transports, actual image-field and Weil
equivalences, exact virtual transport, and WD correction. They are not
attributed to a separate comparison theorem in Tate. The determinant
at `q_E^(-s)` is the existing spectral substitution in the quotient
correction; Tate's auxiliary expression `ε(V) t^(a(V))` is not
identified with the full fixed-additive-character value.

This module constructs one conditional component for the given
embedding `f`. It does not construct an assignment over every finite
extension of `E`, prove that such a family satisfies `IsSystem`, or
prove epsilon-system or reciprocity existence. It does not compare
different closure or embedding choices, or prove composition
coherence. It does not supply a self-dual measure or identify the
Deligne value at an arbitrary Haar measure with Langlands' value.

Only epsilon values are introduced here. The nonzero exponential
coordinate and invertible quotient operator allow the correction at
every complex `s`. No L-factor is evaluated as an everywhere finite
function; the separately published rational L-factors and their
regular-domain evaluations remain the appropriate interfaces for
Euler denominators. Functional equations and completion of the broad
host definition task are not claims of this unit.
