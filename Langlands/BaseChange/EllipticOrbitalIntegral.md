# Functions whose (twisted) orbital integrals vanish off the elliptic set

Module `Langlands.BaseChange.EllipticOrbitalIntegral`
(`Langlands/BaseChange/EllipticOrbitalIntegral.lean`).

This module defines two predicates on functions on `GL_n`: the orbital integrals of a
function vanish at every regular semisimple element that is not regular elliptic, and the
twisted counterpart for the σ-orbital integrals on `GL_n(E)`. It also proves six small
lemmas about them. The predicates follow Kazhdan (1986), printed p. 6 (the space `B(G)`),
Henniart–Lemaire (2011), Chapter II, §II.5.14, Proposition 2 (2) (printed p. 115) and
§II.6.7 (printed p. 123), and Arthur–Clozel (1989), Chapter 1, Lemma 2.12 (ii) (printed
p. 19). Henniart–Lemaire are cited as HL and Arthur–Clozel as AC.

## Setting and conventions

- `F` is a field with a topology making it a topological ring (`[Field F]
  [TopologicalSpace F] [IsTopologicalRing F]`). `E` is a commutative `F`-algebra with a
  topology making it a topological ring, `σ : E ≃ₐ[F] E`, and `l n : ℕ`. No local-field
  hypothesis is made in this module.
- `GL_n(R)` is the Library's `GeneralLinear n R`, and `g^σ = entrywiseAut σ n g`
  (module `Langlands.BaseChange.Norm`).
- `GL_n(F)` and `GL_n(E)` carry a Borel σ-algebra: the definitions take
  `[MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]` (and the same for
  `E`) as instance arguments, exactly as `VanishesOffNorms` of
  `Langlands.BaseChange.OrbitalIntegral` does. Subgroups carry the subspace σ-algebra. Each
  coset space `LeftQuotient H` carries its Borel σ-algebra through the local instances
  `leftQuotientMeasurableSpace` and `leftQuotient_borelSpace` of
  `Langlands.BaseChange.OrbitalIntegral`.
- A right Haar measure on a subgroup `H` is a measure `μH` with `μH.IsHaarMeasure` and
  `μH.IsMulRightInvariant`.
- `orbitalIntegral γ ν f` is the orbital integral `∫ f(x⁻¹ γ x) dν(x)` over
  `G_γ(F) \ GL_n(F)` of `Langlands.TraceFormula.TwistedOrbital`, and
  `sigmaOrbitalIntegral σ n δ ν φ` is HL's twisted orbital integral
  `Λ_σ(φ, δ) = ∫ φ(x⁻¹ δ x^σ) dν(x)` over `G^σ_δ(F) \ GL_n(E)` of
  `Langlands.BaseChange.OrbitalIntegral`. Both are Bochner integrals of the function induced
  on the coset space. The centralizers are `glCentralizer γ` and `sigmaCentralizer σ n δ`
  (same module).
- `IsRegularSemisimple` and `IsRegularElliptic` are the Library's predicates
  (`Langlands/JacquetLanglands/RegularElliptic.lean`): the characteristic polynomial is
  separable, respectively separable and irreducible. `IsSigmaRegular σ l δ` and
  `IsSigmaElliptic σ l δ` (`Langlands.BaseChange.Norm`) say that `δ` is associated, through
  the norm, with a regular semisimple, respectively regular elliptic, element of `GL_n(F)`.
  They need `F` to be a field, which is why `F` is a field here.

## Definitions

1. `OrbitalIntegralsVanishOffElliptic μF f`, for a measure `μF` on `GL_n(F)` (an explicit
   argument, a Haar measure in the intended use) and `f : GL_n(F) → ℂ`. It says: for every
   `γ ∈ GL_n(F)` that is regular semisimple and not regular elliptic, every right Haar
   measure `μγ` on `glCentralizer γ`, and every measure `νγ` on
   `LeftQuotient (glCentralizer γ)` with
   `QuotientIntegration.IsCompatible (glCentralizer γ) μF μγ νγ`, we have
   `orbitalIntegral γ νγ f = 0`.

   Source: Kazhdan (1986, printed p. 6) defines `B(G)` as the set of `f` in
   Harish-Chandra's Schwartz space `𝒞(G)` such that `∫_Ω f(ω) dω = 0` for every regular
   nonelliptic conjugacy class `Ω`. His space `D(G)` of locally constant compactly supported
   functions (printed p. 7) lies in `𝒞(G)`, and for `f ∈ D(G)` definition 1 says that
   `f ∈ B(G)`. HL call such a function "elliptique" (II.6.7, printed p. 123, with reference
   to II.5.14, Proposition 2). The Lean predicate makes sense for every function
   `f : GL_n(F) → ℂ`; the statements of this programme apply it to the underlying function
   of a test function. Kazhdan calls `x` elliptic when the centre of its centralizer is
   compact, in a group with compact centre (printed p. 7, §1.1). For `GL_n`, whose centre is
   not compact, the Library's `IsRegularElliptic` (irreducible characteristic polynomial) is
   the usual counterpart: the centralizer of such an element is the multiplicative group of
   a degree-`n` field extension of `F`, and over a nonarchimedean local field `F` that group
   is compact modulo the centre `F^×`.

2. `SigmaOrbitalIntegralsVanishOffElliptic σ l μE φ`, for a measure `μE` on `GL_n(E)`
   (explicit argument) and `φ : GL_n(E) → ℂ`. It says: for every `δ ∈ GL_n(E)` with
   `IsSigmaRegular σ l δ` and `¬ IsSigmaElliptic σ l δ`, every right Haar measure `μδ` on
   `sigmaCentralizer σ n δ`, and every measure `νδ` on
   `LeftQuotient (sigmaCentralizer σ n δ)` with
   `QuotientIntegration.IsCompatible (sigmaCentralizer σ n δ) μE μδ νδ`, we have
   `sigmaOrbitalIntegral σ n δ νδ φ = 0`.

   Source: this is the conclusion of HL II.5.14, Proposition 2 (2) (printed p. 115:
   `Λ^{G(E)}_σ(φ, δ) = 0` for every σ-regular non-σ-elliptic `δ`) and of the first half of
   AC Chapter 1, Lemma 2.12 (ii) (printed p. 19: the twisted orbital integrals of a
   pseudo-coefficient are `0` on non-σ-elliptic elements).

### The quantification over measures

No measure is chosen or normalized inside the definitions. The Haar measure on `GL_n(F)` or
`GL_n(E)` is an explicit argument, and both predicates quantify over every right Haar
measure on the centralizer and every quotient measure compatible with it, exactly as
`VanishesOffNorms` of `Langlands.BaseChange.OrbitalIntegral` does. This makes the predicates
independent of the normalization of centralizer and quotient measures, which the sources
leave implicit.

The quantifiers are not vacuous. `OrbitalMeasureExistenceStatement`
(`Langlands.BaseChange.OrbitalMeasureExistenceStatement`) asserts, for a nonarchimedean local
field `F`, a cyclic algebra `E` and Haar measures `μF` and `μE`, that every regular
semisimple `γ` has a right Haar measure on `glCentralizer γ`, that every such measure has a
compatible quotient measure, and that every `δ` associated with a regular semisimple `γ` (so
every σ-regular `δ`) has a right Haar measure on `sigmaCentralizer σ n δ` with a compatible
quotient measure. Granting that statement, both predicates constrain actual orbital
integrals.

## Lemmas (with proofs)

3. Closure lemmas.
   - `orbitalIntegralsVanishOffElliptic_zero μF`: definition 1 holds for the zero function.
   - `OrbitalIntegralsVanishOffElliptic.const_mul h c`: if definition 1 holds for `f`, it
     holds for `fun g => c * f g`, for every `c : ℂ`.
   - `sigmaOrbitalIntegralsVanishOffElliptic_zero σ l μE` and
     `SigmaOrbitalIntegralsVanishOffElliptic.const_mul h c`: the same for definition 2.

   Proof. Two private lemmas about the generic twisted orbital integral
   `twistedOrbitalIntegral θ δ ν f = ∫ twistedOrbitFunction θ δ f q dν(q)` of
   `Langlands.TraceFormula.TwistedOrbital` do the work. By induction on the quotient
   (`Quotient.inductionOn`), the orbit function of `0` is the zero function, and the orbit
   function of `c * f` is `c` times that of `f`; both hold by `rfl` on representatives. Then
   `integral_zero` and `integral_const_mul` give `∫ 0 = 0` and `∫ c * u = c * ∫ u`; the
   second holds for Bochner integrals without any integrability hypothesis. Both
   `orbitalIntegral` and `sigmaOrbitalIntegral` unfold to `twistedOrbitalIntegral`, so the
   four lemmas follow by applying the hypothesis to the same `γ` (or `δ`) and measures.

4. Rank one.
   - `isRegularElliptic_of_isRegularSemisimple_one g hg`: every `g : GL_1(F)` with
     `IsRegularSemisimple g` satisfies `IsRegularElliptic g`. This holds for every field `F`
     (no topology is used).
   - `orbitalIntegralsVanishOffElliptic_one μF f`: definition 1 holds for every measure `μF`
     on `GL_1(F)` and every `f : GL_1(F) → ℂ`, since there is no regular semisimple element
     of `GL_1(F)` that is not regular elliptic.

   Proof. `IsRegularElliptic g` is `IsRegularSemisimple g` together with the irreducibility
   of the characteristic polynomial. The characteristic polynomial of a `1 × 1` matrix has
   degree `1` (`Matrix.charpoly_degree_eq_dim` and `Fintype.card_fin`), and a polynomial of
   degree `1` over a field is irreducible (`Polynomial.irreducible_of_degree_eq_one`). The
   second lemma derives a contradiction from the hypothesis `¬ IsRegularElliptic γ`.

## Dependencies

The module imports `Langlands.BaseChange.OrbitalIntegral`, which brings in
`Langlands.BaseChange.Norm`, `Langlands.TraceFormula.TwistedOrbital`, the Library's
`Langlands.JacquetLanglands.RegularElliptic` and the quotient-measure conventions of
`Langlands/Analysis/Local/QuotientMeasure.lean` (`QuotientIntegration.IsCompatible`) and
`Langlands/Group/LeftQuotient.lean` (`LeftQuotient`). It defines no new notion of orbital
integral, twisted orbital integral or ellipticity.
