# Twisted characters of σ-discrete series on the σ-elliptic set: a reduction

The module `Langlands.BaseChange.SigmaDiscreteEllipticNonvanishingReduction` proves that
`SigmaDiscreteEllipticNonvanishingStatement` follows from the existence of test functions with
σ-elliptic orbital integrals and from the local integrability of twisted characters. It follows
Arthur–Clozel's proof of Lemma 2.12 (i) in Chapter 1, without the twisted Weyl integration
formula: the Library's comparison of integrals of concordant functions takes its place.

## Statement

`SigmaDiscreteEllipticNonvanishingReductionStatement.{u, v, uW}` is the implication

`SigmaDiscreteEllipticOrbitalTestStatement.{u, v, uW} →
TwistedCharacterLocalIntegrabilityStatement.{u, v, uW} →
SigmaDiscreteEllipticNonvanishingStatement.{u, v, uW}`

with the same universe parameters for the field `F`, the cyclic extension `E` and the
representation space `W` in the premises and in the conclusion. The three propositions are in
the Library:

- `SigmaDiscreteEllipticOrbitalTestStatement` (module
  `Langlands.BaseChange.SigmaDiscreteEllipticOrbitalTestStatement`): for a nonarchimedean local
  field `F` of characteristic zero, a field `E` that is a cyclic `F`-algebra of group `⟨σ⟩` of
  order `l`, a σ-discrete series `τ` of `GL_{r+1}(E)`, an isomorphism `A` of `τ` onto `τ^σ` and a
  Haar measure `μ`, some test function has σ-orbital integrals vanishing at the σ-regular
  elements that are not σ-elliptic and nonzero twisted trace `tr(τ(φ) ∘ A)`.
- `TwistedCharacterLocalIntegrabilityStatement` (module
  `Langlands.BaseChange.TwistedCharacterLocalIntegrabilityStatement`): for an irreducible
  admissible `τ` and `A` as above, the twisted character is represented by a function `Θ`,
  locally integrable for every Haar measure and locally constant near every σ-regular element
  (Clozel 1987, Theorem 1; Arthur–Clozel 1989, Chapter 1, Proposition 2.2).
- `SigmaDiscreteEllipticNonvanishingStatement` (module
  `Langlands.BaseChange.SigmaDiscreteEllipticNonvanishingStatement`): in the setting of the first
  statement, some test function supported in the σ-elliptic set has nonzero twisted trace.

The theorem `sigmaDiscreteEllipticNonvanishingReduction` proves the implication.

## Auxiliary results

- `concordantIntegrableIntegralEquality : ConcordantIntegrableIntegralEqualityStatement.{u, v}`:
  for integrable `φ` on `GL_n(E)` and `f` on `GL_n(F)` that are concordant
  (`AreConcordant`, Henniart–Lemaire I.2.5), `∫ φ = ∫ f`. It is
  `concordantIntegralComparisonReduction` (module `Langlands.BaseChange.ConcordantIntegralComparison`)
  applied to the Library theorems `ordinaryWeylHaarLocalPushforwards`,
  `twistedWeylHaarLocalPushforwards`, `regularSemisimpleOpenConull` and `sigmaRegularOpenConull`.
- `integral_eq_zero_of_sigmaOrbitalIntegral_eq_zero`: for a cyclic algebra `E`, a Haar measure
  `μ` on `GL_n(E)` and an integrable `φ` whose σ-orbital integrals vanish at every σ-regular
  element, for every right Haar measure on the σ-centralizer and every compatible quotient
  measure, `∫ φ dμ = 0`. With a Haar measure on `GL_n(F)` (Borel σ-algebra), `φ` is concordant
  with the zero function: the orbital integrals of `0` vanish, and at an associated pair `(δ, γ)`
  with `γ` regular semisimple, `δ` is σ-regular. Then `concordantIntegrableIntegralEquality`
  gives `∫ φ dμ = 0`.
- `TwistedCuspidalPseudoCoefficientExistenceStatement.sigmaDiscreteEllipticOrbitalTest`: the
  Library's `TwistedCuspidalPseudoCoefficientExistenceStatement` implies
  `SigmaDiscreteEllipticOrbitalTestStatement` at the same universe parameters. A σ-discrete
  series is tempered (`IsTemperedRep`), and temperedness for a Haar measure on the central
  quotient supplies a unitary central character `χ` (`UnitaryCentralCharacter`), so
  `HasCentralCharacterRep τ χ`. Part (a) of the existence statement gives twisted trace `1`
  (`IsTwistedPseudoCoefficient`), and part (c) gives the orbital vanishing.

## Proof of the implication

Fix `F`, `E`, `σ`, `l`, `r`, `τ`, `A` and a Haar measure `μ` on `GL_{r+1}(E)`. Let `φ₀` be a test
function given by `SigmaDiscreteEllipticOrbitalTestStatement`, and `Θ` the twisted character
function given by `TwistedCharacterLocalIntegrabilityStatement` (`τ` is irreducible).

1. **Invariance of `Θ`.** For σ-regular `δ` and every `x`, `Θ(x⁻¹ δ x^σ) = Θ(δ)`. The element
   `x⁻¹ δ x^σ` is σ-regular (`IsNormAssociated.twistedConj`, module `Langlands.BaseChange.Norm`).
   `Θ` is locally constant at both points, so `IsTwistedCharacterFunction.hasTwistedCharacterValue`
   (module `Langlands.BaseChange.CharacterFunction`) gives local twisted character values `Θ(δ)`
   and `Θ(x⁻¹ δ x^σ)` there. The value at `δ` is also a value at `x⁻¹ δ x^σ` by
   `HasTwistedCharacterValue.twistedConj` (module `Langlands.BaseChange.TwistedCharacter.Saturation`,
   with the intertwining relation `A ∘ τ(g) = τ(g^σ) ∘ A`). Local values are unique
   (`HasTwistedCharacterValue.unique`).
2. **A nonzero value on the σ-elliptic set gives the witness.** If `Θ(δ) ≠ 0` for some σ-elliptic
   `δ`, then `δ` is σ-regular, the twisted distribution has the local value `Θ(δ)` at `δ`, and the
   σ-elliptic set is open (`isOpen_setOf_isSigmaElliptic`, module
   `Langlands.BaseChange.EllipticLocusClopen`). The lemma
   `exists_support_subset_ne_zero_of_hasLocalValue` (module
   `Langlands.BaseChange.TwistedTraceRegularNonvanishingReduction`) then gives a test function
   supported in the σ-elliptic set with nonzero twisted trace: the indicator of a compact open
   neighbourhood `K` of `δ` inside the σ-elliptic set and the neighbourhood of the local value has
   twisted trace `Θ(δ) μ(K)`, and `0 < μ(K) < ∞`.
3. **Otherwise a contradiction.** Suppose `Θ` vanishes at every σ-elliptic element. The product
   `φ₀ Θ` is integrable (`Θ` is locally integrable and `φ₀` is continuous with compact support),
   and `∫ φ₀ Θ dμ = tr(τ(φ₀) ∘ A)`. At a σ-regular `δ`, step 1 turns the σ-orbital integrand of
   `φ₀ Θ` into `Θ(δ)` times that of `φ₀`, so the σ-orbital integral of `φ₀ Θ` (for any right Haar
   measure and compatible quotient measure) is `Θ(δ)` times that of `φ₀`. If `δ` is σ-elliptic,
   `Θ(δ) = 0`; otherwise the σ-orbital integral of `φ₀` vanishes. By
   `integral_eq_zero_of_sigmaOrbitalIntegral_eq_zero`, `tr(τ(φ₀) ∘ A) = ∫ φ₀ Θ dμ = 0`, which
   contradicts the choice of `φ₀`.

## Sources

- J. Arthur, L. Clozel, *Simple algebras, base change, and the advanced theory of the trace
  formula*, Ann. of Math. Stud. 120 (1989), Chapter 1, Lemma 2.12 and its proof, printed p. 19:
  for a pseudo-coefficient `φ` of a σ-discrete `Π`, the identity
  `1 = tr(Π(φ) I_σ) = ∫ Θ_{Π,σ}(g) φ(g) dg`, together with the vanishing of the twisted orbital
  integrals of `φ` off the σ-elliptic set, shows that `Θ_{Π,σ}` does not vanish identically on the
  σ-elliptic set. The source passes through the twisted Weyl integration formula; the Lean proof
  uses instead the comparison of integrals of concordant functions with the zero function on
  `GL_n(F)`, which the Library derives from the local pushforward identities of the twisted and
  ordinary Weyl maps.
- G. Henniart, B. Lemaire, *Changement de base et induction automorphe pour GL_n en
  caractéristique non nulle*, Mém. SMF 124 (2011), II.5.14, Corollaire 2 and its proof, printed
  p. 117 (the same argument, with II.2.10, formula (1), printed p. 72), and I.2.5, printed
  pp. 17–18, for concordance.
- The passage from a nonzero value of the character function at a σ-elliptic point to a test
  function supported in the σ-elliptic set uses the openness of that set and the local constancy
  of the character function there (Henniart–Lemaire 2011, II.1.2, printed pp. 55–56, for the
  σ-elliptic set).
