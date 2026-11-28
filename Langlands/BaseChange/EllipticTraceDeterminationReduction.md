# Elliptic determination of traces from local integrability of characters

The module `Langlands.BaseChange.EllipticTraceDeterminationReduction` states and proves that
Harish-Chandra's local integrability theorem for the characters of `GL_n(F)` implies the
elliptic determination of traces.

## Statement

`EllipticTraceDeterminationFromLocalIntegrabilityStatement.{u, uI, uV}` is the implication

`CharacterLocalIntegrabilityStatement.{u, uV} → EllipticTraceDeterminationStatement.{u, uI, uV}`

with the same field universe `u` and the same universe `uV` of representation spaces in the
premise and in the conclusion; `uI`, the universe of the finite index type, occurs only in the
conclusion. Both propositions are in the Library:

- `CharacterLocalIntegrabilityStatement` (module
  `Langlands.BaseChange.CharacterLocalIntegrabilityStatement`): for a nonarchimedean local field
  `F` of characteristic zero and every `n`, the character of every irreducible admissible
  representation `ρ` of `GL_n(F)` is represented by a function `Θ` (`IsCharacterFunction`,
  module `Langlands.BaseChange.CharacterFunction`: `Θ` is locally integrable for every Haar
  measure `μ` and `tr ρ(f) = ∫ f Θ dμ` for every Schwartz–Bruhat `f`) that is locally constant
  near every regular semisimple element (Harish-Chandra 1999, Theorem 16.3).
- `EllipticTraceDeterminationStatement` (module
  `Langlands.BaseChange.EllipticTraceDeterminationStatement`): for such `F`, `0 < n` and a Haar
  measure `μ` on `GL_n(F)`, if a finite combination `∑ i, a i * tr ρ_i(f)` of the characters of
  irreducible admissible representations vanishes on every Schwartz–Bruhat `f` supported in the
  regular elliptic set, then it vanishes on every Schwartz–Bruhat `f` with
  `OrbitalIntegralsVanishOffElliptic μ f` (the orbital integrals of `f` vanish at every regular
  semisimple element that is not regular elliptic).

The theorem `ellipticTraceDeterminationFromLocalIntegrability` proves the implication. This
module does not prove `CharacterLocalIntegrabilityStatement`; the hypothesis `0 < n` of the
conclusion is not used by the proof.

## Auxiliary result

`eq_zero_of_forall_integral_mul_eq_zero`: on a Hausdorff, locally compact, totally disconnected
space with a Borel measure `μ` that is finite on compact sets and positive on nonempty open sets,
let `Θ` be constant near a point `x` and let `U` be an open set containing `x`. If
`∫ φ Θ dμ = 0` for every Schwartz–Bruhat `φ` supported in `U`, then `Θ x = 0`. The proof takes
a compact open neighbourhood `K` of `x` inside `U` on which `Θ` is constant
(`exists_isCompact_isClopen_subset`, module `Langlands.JacquetLanglands.LocalCharacter`) and
`φ` its indicator (`Hecke.TestFunction.characteristic`); then `∫ φ Θ dμ = μ(K) Θ x` with
`0 < μ(K) < ∞`.

## Proof of the implication

Fix `F`, `n`, `μ`, the representations `ρ i` (`i ∈ I`), the coefficients `a i`, and a
Schwartz–Bruhat `f` with `OrbitalIntegralsVanishOffElliptic μ f`. The premise gives, for each
`i`, a character function `Θ i` of `ρ i`, locally constant near the regular semisimple
elements. Put `Θ = ∑ i, a i * Θ i`.

1. *Traces as integrals.* For every Schwartz–Bruhat `φ`, each `φ Θ i` is integrable (a locally
   integrable function times a continuous compactly supported one), so
   `∑ i, a i * tr ρ_i(φ) = ∫ φ Θ dμ`.
2. *Local constancy and conjugation invariance.* `Θ` is locally constant near every regular
   semisimple `t` (finitely many neighbourhoods). If `t` and `x⁻¹ t x` are regular semisimple,
   then `Θ i (x⁻¹ t x) = Θ i t`: both are character values of `ρ i` in the sense of
   `HasCharacterValue` (`IsCharacterFunction.hasCharacterValue`), the value at `t` is also a
   value at `x⁻¹ t x` by `HasCharacterValue.conjugate` (module
   `Langlands.BaseChange.CharacterLocalValueConjugation`), and character values are unique
   (`HasCharacterValue.unique`).
3. *Vanishing on the regular elliptic set.* The regular elliptic set is open
   (`isOpen_regularElliptic`, module `Langlands.BaseChange.RegularEllipticOpen`). A test function
   supported in it is elliptically supported, so by the hypothesis and step 1 `∫ φ Θ dμ = 0` for
   all such `φ`; by `eq_zero_of_forall_integral_mul_eq_zero`, `Θ γ = 0` at every regular
   elliptic `γ`.
4. *Weyl decomposition.* The function `g = f Θ` is integrable. Its integral equals its integral
   over the regular semisimple set, whose complement is null (`regularSemisimpleOpenConull`,
   module `Langlands.BaseChange.RegularSetOpenConull`). Choose a set `S` of representatives of
   the conjugacy classes of maximal tori (`WeylTorus.exists_isRepresentativeSet`) and, for each
   torus `T`, a Haar measure on `T(F)` with a compatible measure `ν_T` on `T(F) \ GL_n(F)`
   (`WeylTorus.exists_ordinaryMeasures`, both in module
   `Langlands.BaseChange.ConcordantIntegralComparison`). The local Haar pushforward identities
   (`ordinaryWeylHaarLocalPushforwards`) and the ordinary Weyl decomposition
   (`ordinaryWeylIntegralDecomposition`, module
   `Langlands.BaseChange.OrdinaryWeylIntegralDecomposition`), with the weight given by the
   absolute value of the Weyl discriminant (positive and locally constant on the regular points
   by `det_ordinaryWeylDifferential`, `discriminantWeight_pos` and
   `isLocallyConstant_discriminantWeight`), write
   `∫ g dμ` as the sum over `T ∈ S` of the integrals over the regular points `t` of `T(F)` of
   `|W_T|⁻¹ |D(t)| ∫ g(x⁻¹ t x) dν_T(x)`.
5. *Each term vanishes.* Let `t` be a regular point of a torus `T`. Every `x⁻¹ t x` is regular
   semisimple (`isRegularSemisimple_ordinaryOrbitMap`), so by step 2
   `g(x⁻¹ t x) = Θ t · f(x⁻¹ t x)` and the inner integral is `Θ t · ∫ f(x⁻¹ t x) dν_T(x)`. If
   `t` is regular elliptic, `Θ t = 0` by step 3. Otherwise
   `WeylTorus.exists_orbitalIntegral_eq` identifies `∫ f(x⁻¹ t x) dν_T(x)` with the orbital
   integral `orbitalIntegral t ν f` for a right Haar measure on the centralizer `G_t(F) = T(F)`
   and a compatible quotient measure `ν`, and this orbital integral is `0` by
   `OrbitalIntegralsVanishOffElliptic μ f`. Hence every term, and the sum, is `0`, and
   `∑ i, a i * tr ρ_i(f) = ∫ f Θ dμ = 0`.

The proof uses the Library's decomposition of integrals over the regular semisimple set and does
not use `WeylIntegrationFormulaStatement`.

## Sources

- Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, notes by
  DeBacker and Sally, ULS 16, AMS 1999, source ID
  `harish-chandra-1999-admissible-invariant-distributions`, Theorem 16.3, printed p. 75: the
  character of an admissible irreducible representation is a locally summable function, locally
  constant on the regular set. This is the premise.
- Henniart–Lemaire, *Changement de base et induction automorphe pour `GL_n` en caractéristique
  non nulle*, Mém. SMF 124 (2011), source ID
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`, II.2.10,
  formula (2), printed p. 72: for a locally integrable `θ` on `G(F)` invariant under conjugation
  at almost every regular element, `∫ f θ = ∑_T |W_T(F)|⁻¹ ∫_{T(F)} |D_G(γ)|_F Λ(f, γ) θ(γ) dγ`.
  Steps 4 and 5 are this formula for `θ = Θ`, obtained from the Library's decomposition and the
  pointwise conjugation invariance of step 2.
- Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace Formula*
  (1989), source ID `arthur-clozel-1989-base-change`, Chapter 1, proof of Lemma 2.12, printed
  p. 19: for a pseudo-coefficient `φ` whose twisted orbital integrals vanish off the σ-elliptic
  set, the identity `1 = trace(Π(φ) I_σ) = ∫ Θ_{Π,σ}(g) φ(g) dg` is used to relate traces to the
  values of the twisted character on the σ-elliptic set. The present module carries out the
  corresponding ordinary argument for finite combinations of characters of `GL_n(F)`.
