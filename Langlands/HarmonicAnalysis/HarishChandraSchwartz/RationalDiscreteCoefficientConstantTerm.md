# Discrete-series coefficients have vanishing constant terms

Let `A` be a smooth representation of `G(F)` that is square integrable modulo
the image `A_G(F)` of a split component. Let `U` be the unipotent radical of a
proper standard parabolic `P = M U`. This module proves that every coefficient
of `A` integrates to zero over `U` along every two-sided translate,
provided these integrals converge absolutely. Absolute convergence is a
hypothesis here; the module does not prove it.

## Provenance

Waldspurger (2003) proves the corresponding inclusion of coefficient spaces in
VIII.4, printed p.330 (PDF p.96): the coefficients of discrete series with
central character `χ` lie in `p_χ(°C(G))`. His argument goes through wave
packets and Theorem VII.2.5. By Lemma VIII.2.1, printed p.321 (PDF p.87), a
Schwartz function `f` lies in `°C(G)` exactly when `f^{(P),Ind} = 0` for every
proper semistandard parabolic `P = M U`. The operator `f ↦ f^{(P),Ind}` is
defined in §III.6, printed p.272 (PDF p.38). It is built from the ordinary
normalized integral over `U`,
`f^{(P)}(m) = δ_P(m)^{1/2} ∫_U f(m u) du`, applied to all two-sided
translates: `f^{(P),Ind}(g₁, g₂) = (ρ(g₁) λ(g₂) f)^{(P)}`. It is not the weak
constant term, which §III.5 (printed pp.270–271, PDF pp.36–37) defines
separately.

The theorems below concern this ordinary integral. They prove that the ordinary
integral over `U` vanishes along every two-sided translate, for the radicals
`U` of proper standard parabolics. This is the condition
`IsIntegrableUnipotentCuspidal` that defines the Library's integrable cuspidal
kernel (module `RationalCuspidalSpace`). The published
`isIntegrableUnipotentCuspidal_iff_constantTermInd` in that module compares it
with `f^{(P),Ind}`: when all translates are integrable over `U`, the condition
is equivalent to the vanishing of the Library's induced constant term
`constantTermInd`. Waldspurger gets convergence of the integrals for Schwartz
functions from Proposition II.4.5. Here absolute integrability is an explicit
hypothesis.

This module takes a different and more direct route, internal to the Library.
It uses Casselman's criterion, Waldspurger Proposition III.1.1, printed p.263
(PDF p.29), cited there as [C, Théorème 4.4.6]. Let `π` be square integrable and
`P = M U` semistandard. Then every exponent `χ ∈ Exp(π_P)` of the Jacquet
module satisfies `Re(χ) ∈ +a^{G*}_P`. This is the open cone of the sums
`∑_{α ∈ Δ(P)} x_α α` with all `x_α > 0` (§I.1, printed p.239, PDF p.5).
Waldspurger's sign convention is `q^{-⟨χ, H_G(g)⟩} = |χ|_F(g)` (§I.1, printed
pp.239–240, PDF pp.5–6). So for `a` in the split center `A_M` of `M`,
`|χ(a)| = q^{-⟨Re(χ), H_M(a)⟩}`. Suppose `⟨α, H_M(a)⟩ ≥ 0` for every
`α ∈ Δ(P)`, with strict inequality for at least one `α`. Then
`⟨Re(χ), H_M(a)⟩ > 0`, hence `|χ(a)| < 1`.

The Library implements this consequence in two steps.
`hasStrictNormalizedJacquetExponents_universeLift` (module
`RationalSquareIntegrableDecayProof`) supplies the strict exponents of the
normalized Jacquet modules. `rationalLatticeStrictExponent` evaluates them at
one central element `z` of the standard Levi with
`z = uniformizerPowers i (.ofAdd ζ)`, the uniformizer point of a cocharacter
`ζ`. Here `ζ` pairs to zero with the simple roots in `I` (those of the Levi),
nonnegatively with all simple roots, and positively with at least one. The
output is `‖χ(z)‖ < 1` for every central exponent `χ` of the normalized Jacquet
module. The argument is:

1. The form `B(v, ℓ) = ∫_U ℓ(A(u) v) du` is invariant under `U` acting on
   either variable. So it descends to the `U`-coinvariants of `A` and of its
   smooth contragredient.
2. Under the diagonal action of `M`, the form scales by the Haar modulus of
   conjugation on `U`. The normalization `δ_P^{-1/2}` of both Jacquet modules
   cancels this factor, so `B` is invariant under the two normalized Jacquet
   actions.
3. Both normalized Jacquet modules are admissible. Choose a central element
   `z` of `M` at which every central exponent of both modules has absolute
   value `< 1`. On generalized eigenvectors with eigenvalues `a` and `b`,
   invariance under `z` forces `B = 0` unless `a b = 1`, and that is
   impossible here. The generalized eigenvectors span both modules, so
   `B = 0`.

The PDF page is the printed page minus 234.

## Invariant forms on generalized eigenvectors

Section `GeneralizedEigenPairing`.

- `bilinear_eq_zero_of_genEigen`: let `β : X →ₗ Y →ₗ ℂ` be bilinear and
  invariant under endomorphisms `T` of `X` and `S` of `Y`, meaning
  `β (T x) (S y) = β x y`. Let `a b : ℂ` with `a * b ≠ 1`. If
  `(T - a)^n x = 0` and `(S - b)^m y = 0`, then `β x y = 0`. The proof is by
  induction on `n` and `m`: `(1 - a b) β x y` is a combination of values of
  `β` at lower depth.

## Change of variables under conjugation

Section `Conjugation`. `Γ` is a topological group and `U` a locally compact
subgroup with a Borel structure.

- `mulEquivHaarChar_congr`: the Haar character `mulEquivHaarChar φ` of a
  topological automorphism `φ` does not depend on which of two Borel
  measurable structures is used.
- `integral_conj_symm`: for `g` in the normalizer of `U`, a regular Haar
  measure `mu` on `U` and `f : U → ℂ`, the integral of `u ↦ f (c_g⁻¹ u)` is
  `mulEquivHaarChar c_g • ∫ f`. Here `c_g` is the conjugation
  `HaarModulus.normalizerConj U g`.

## The radical pairing

Section `RadicalPairing`. Data: two representations `ρ₁`, `ρ₂` of `Γ` on
complex vector spaces `X`, `Y`, a bilinear form `p : X →ₗ Y →ₗ ℂ`, and a
measure `mu` on `U`.

- `IsRadicalIntegrable U mu ρ₁ p` (definition): every function
  `u ↦ p (ρ₁ u x) y` is `mu`-integrable.
- `radicalPairing hint` (definition): the bilinear form
  `(x, y) ↦ ∫_U p (ρ₁ u x) y d mu`. `radicalPairing_apply` unfolds it.
- `radicalPairing_right`: for a right-invariant `mu`, replacing `x` by
  `ρ₁ u₀ x` with `u₀ ∈ U` does not change the pairing.
- `radicalPairing_left`: if `mu` is left invariant and `p` is invariant
  (`p (ρ₁ g x) (ρ₂ g y) = p x y`), replacing `y` by `ρ₂ u₀ y` does not change
  the pairing.
- `radicalPairing_conj`: for `U` locally compact, `mu` a regular Haar measure,
  `p` invariant and `g` in the normalizer of `U`, the pairing of
  `ρ₁ g x` and `ρ₂ g y` is `mulEquivHaarChar c_g` times the pairing of `x`
  and `y`.

## Descent to Jacquet modules

Section `JacquetPairing`.

- `jacquetPairing hint hp` (definition): for a Haar measure `mu` that is both
  left and right invariant, the radical pairing as a bilinear form on the
  `U`-coinvariants `Jacquet.Localization.Coinvariants ρ₁ U 1` and
  `Jacquet.Localization.Coinvariants ρ₂ U 1`. It is built with
  `Jacquet.Localization.lift` from the two previous invariances.
- `jacquetPairing_mk`: on the classes of `x` and `y` it is
  `radicalPairing hint x y`.

## Vanishing from strict central exponents

Section `StrictExponents`. `M` is a topological group.

- `bilinear_eq_zero_of_strictExponents`: let `ρ₁`, `ρ₂` be smooth
  center-finite representations of `M` and `β` a bilinear form invariant under
  a central element `z`. Suppose every central exponent `χ` of either
  representation (`IsCentralExponent`) has `‖χ z‖ < 1`. Then `β = 0`. The
  generalized central character spaces span both representations
  (`CentralDecomposition.smooth_spanning`). On a pair of such spaces, a nonzero
  vector makes the character a central exponent. The two eigenvalues of `z`
  then have product of norm `< 1`, so `bilinear_eq_zero_of_genEigen` applies.

## Normalized Jacquet modules

Section `NormalizedJacquet`. `Γ` is a locally compact nonarchimedean group.
`U` is a closed subgroup with a regular, right-invariant Haar measure `mu`.
`M ≤ normalizer U`, and `A₁`, `A₂` are smooth representations with a bilinear
form `p` invariant under `Γ`. The functor is the published
`Aubert.General.normalizedJacquetFunctor U M hU hMU`.

- `normalizedJacquetPairing M hU hMU hint hp` (definition): the Jacquet
  pairing, viewed on the two normalized Jacquet modules. These have the same
  underlying spaces of coinvariants. `normalizedJacquetPairing_mk` evaluates
  it on classes.
- `normalizedJacquetPairing_invariant`: the pairing is invariant under the
  normalized actions of every `m ∈ M`. The normalized action is the
  coinvariant action of `m` times the scalar `c =
  HaarModulus.closedInverseHalfCharacter U hU M hMU m`. By
  `radicalPairing_conj` the pairing picks up the factor `c² · δ(m)`, where
  `δ(m)` is `mulEquivHaarChar` of conjugation by `m`. By
  `Jacquet.inverseHalfCharacter_sq`, `c²` is the inverse of the published
  modulus `HaarModulus.closedRestrictCharacter U hU M hMU m`. That modulus
  equals `δ(m)` by `mulEquivHaarChar_congr`. So `c² · δ(m) = 1`.
- `radicalPairing_eq_zero_of_strict`: suppose both normalized Jacquet modules
  are admissible. Suppose also that, for one `z` in the center of `M`, every
  central exponent of either module has `‖χ z‖ < 1`. Then
  `radicalPairing hint x y = 0` for all `x`, `y`. Admissible modules are
  center-finite (`CentralDecomposition.admissible_centerFinite`), and the
  previous two items combine.

## The evaluation pairing on universe lifts

Section `EvaluationPairing`.

- `liftedEvaluation A` (definition): for `A : SmoothRep.{0, uG, uV} ℂ Γ`, the
  evaluation pairing `(v, ℓ) ↦ ℓ(v)` between the universe lifts
  `SmoothRep.universeLift.{uW} A` and
  `SmoothRep.universeLift.{uW} A.contragredient`. It transports
  `smoothDualPairing` along `SmoothRep.universeLiftEquiv`.
- `liftedEvaluation_apply`: on lifts of `v` and `ℓ` it is `ℓ.val v`.
- `liftedEvaluation_invariant`: it is invariant under the diagonal action of
  `Γ` (`smoothDualPairing_invariant`).

The universe lift is needed because the published rational strict-exponent
interface `rationalLatticeStrictExponent` takes representations whose carrier
universe is `max (u + 1) v`. The rational theorems use
`SmoothRep.universeLift.{u + 1}` (module `UniverseLift`). It sends
`A : SmoothRep.{0, u, uV} ℂ G(F)` to a representation with carrier universe
`max uV (u + 1)`, so the independent source universe `uV` is kept.

## Rational points

Section `Rational`. The setting and local instances are those of
`RationalSquareIntegrableDecay`:

- a nonarchimedean local field `F`;
- a connected reductive `G` (`hG`) with maximal split torus `i` (`hi`);
- a generic cocharacter `ν` (`hν`);
- a split component `s` (`hs`), with the Borel structure on
  `G(F) / A_G(F)` and a Haar measure `mu` there.

Each theorem has these remaining hypotheses:

- `A : SmoothRep.{0, u, uV} ℂ (rationalPoints G)` is square integrable modulo
  `A_G(F)`: `IsSquareIntegrableModCentralSubgroup … A.representation mu`;
- `I` is a finite set of simple roots with `rootSet i ν I ≠ simpleRelativeRoots
  i ν`, so the standard parabolic of `I` is proper;
- `muU` is a Haar measure on `standardUnipotentPoints i ν (rootSet i ν I)`;
- integrability: for every `v` and every smooth functional `ℓ`, the function
  `u ↦ ℓ.val (A.representation u v)` is `muU`-integrable.

The theorems:

- `integral_unipotent_coefficient_eq_zero`: under these hypotheses,
  `∫ u, ℓ.val (A.representation u v) d muU = 0` for all `v` and `ℓ`.
  The proof:
  - The contragredient is square integrable as well
    (`IsSquareIntegrableModCentralSubgroup.smoothContragredient`), because
    `mu` is inversion invariant (`rationalSplitCentralQuotientHaar_invariant`).
  - `standardCocharacter` gives a cocharacter `ζ` adapted to `rootSet i ν I`.
    It pairs to zero with the roots of `I` and is nonnegative on all simple
    roots. It is positive on one simple root, since `I` is proper.
  - `muU` is regular, since `U` is closed, second countable and metrizable. It
    is right invariant, since every compact set lies in a compact subgroup
    (`isMulRightInvariant_of_forall_isCompact_subgroup`,
    `standardUnipotentPoints_isLimitOfCompactSubgroups`).
  - `rationalLatticeStrictExponent` provides a central element `z` of the
    standard Levi `levi i ν I` at which all central exponents of the
    normalized Jacquet module of the universe lift have norm `< 1`. It is
    applied to `A` and to its contragredient, with the strict exponents from
    `hasStrictNormalizedJacquetExponents_universeLift`. Both applications
    produce the same `z`, which is determined by `ζ`.
  - Both normalized Jacquet modules are admissible
    (`isAdmissible_jacquetFunctor_obj_of_iwahoriContraction`, using the
    contraction basis of `dynamic_hasOppositeIwahoriContractionBasis` for
    `ζ`).
  - `radicalPairing_eq_zero_of_strict` with `p = liftedEvaluation A` gives
    the vanishing on the universe lifts. By `liftedEvaluation_apply` this is
    the stated integral.
- `isIntegrableUnipotentCuspidal_coefficientTensorMap`: for every
  `t : CoefficientTensor A`, the function `coefficientTensorMap A t` satisfies
  `IsIntegrableUnipotentCuspidal muU` (module `RationalCuspidalSpace`): every
  two-sided translate `u ↦ f (x u y)` is `muU`-integrable with integral zero.
  For a pure tensor `v ⊗ ℓ`, `f (x u y)` is the coefficient of the vector
  `A y v` and the functional `A^∨(x⁻¹) ℓ` at `u`. So integrability is the
  hypothesis and the vanishing is the previous theorem. General tensors follow
  by additivity, since `integrableUnipotentCuspidalSubmodule muU` is a
  submodule.
- `coefficientFunctionSpace_le_integrableUnipotentCuspidalSubmodule`: the
  coefficient space `coefficientFunctionSpace A` (Waldspurger's `A(π)`,
  module `CoefficientIndependence`) is contained in
  `integrableUnipotentCuspidalSubmodule muU`. Each spanning coefficient
  `matrixCoefficient A.representation ℓ.val v` is
  `coefficientTensorMap A (v ⊗ ℓ)`.
