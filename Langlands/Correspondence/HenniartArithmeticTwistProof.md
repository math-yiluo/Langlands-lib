# Unramified twists of arithmetic pair factors

Author: Worker 4803. Module `Langlands.Correspondence.HenniartArithmeticTwistProof`,
namespace `Langlands.Henniart.Extension`. The field universe `uK` and the Weil
carrier universe `uW` are independent.

This module proves `ArithmeticPairUnramifiedTwistStatement.{uK, uW}` (stated in
`HenniartExtensionInputs`) with the standard axioms only, as
`arithmeticPairUnramifiedTwist`. It has no new statement. The theorem is used by
`SupercuspidalCorrespondenceHenniartReducedStatement` (module
`HenniartCorrespondenceReduction`).

Notation: `ν` is the local norm character, `I` the local inertia subgroup, `Φ` the
published geometric Frobenius lift `localGeometricFrobenius K` (degree one),
`χ_z = localUnramifiedCharacter K z` (value `z ^ deg`), `ι` the inclusion of the
subgroup fixing the bottom intermediate field `baseExtension K`, and `q` the
residue cardinality of `K`.

## How the proof goes

The classes `weilPairClass K σ` and `weilPairClass K σ_z` of a representative `A₀`
are, by definition, the classes of `zeroMonodromy ν A₀` and of
`zeroMonodromy ν (twist χ_z A₀)`. So the statement reduces to the two
representative-level theorems below.

### L-factors: `arithmeticPairLFactor_unramifiedTwist`

The arithmetic pair L-factor of two zero-monodromy pairs is the rational L-factor
of their tensor at `(I, Φ)`.

- `tensorTwistOneEquiv` and `tensorTwistMulEquiv` give pair equivalences from
  `zM A₀ ⊗ zM B₀` to `zM (1·A₀) ⊗ zM (1·B₀)`, and from
  `zM (χ_z A₀) ⊗ zM (χ_{z'} B₀)` to `zM (χ_z χ_{z'} A₀) ⊗ zM (1·B₀)`. They are
  assembled from the published `FiniteRepresentation.tensorTwistEquiv`,
  `FiniteRepresentation.twistEquivOfEq`, `FiniteRepresentation.twistOneEquiv`,
  `WeilDeligneRepresentation.tensorEquiv` and `zeroMonodromyEquivOfEquiv`.
- The published `rationalLFactor_zeroTensorTwist` (an inertia-trivial twist of the
  first factor scales the Frobenius operator `M` on the inertia invariants of
  `A₀ ⊗ (1·B₀)`) gives the factors `R(M)` and `R(z z' M)`, where `R(T)` is
  `1 / det(1 - X T)`. The characters are trivial on inertia
  (`localUnramifiedCharacter_inertia`) and take the values `z` and `z'` at `Φ`
  (`localUnramifiedCharacter_frobenius`).
- `eulerPolynomial_smul`, imported from [Euler/Scaling](../LocalFactor/Euler/Scaling.md): `det(1 - X (c T)) = det(1 - X T)` evaluated at `c X`.
  Two polynomials over `ℂ` agree when they agree at every point
  (`Polynomial.funext`), and both evaluate to `det(1 - c x T)`.
- If `R(M) = 1 / P`, then `det(1 - X M) = P`: inversion is injective, and so is
  the map from polynomials to rational functions. Hence the twisted factor is
  `1 / P(z z' X)`.

### Epsilon certificates: `isArithmeticPairEpsilonFactor_unramifiedTwist`

The published spectral epsilon value at `s` is the supplied system evaluated at
the spectral twist by `s` (`conditionalDeligneValue`), times a quotient
correction that equals one for zero monodromy. So twisting by an unramified
character shifts `s`. No further property of the system is used.

- `exists_spectralExponent`: for `t = z z'` there is `s₀` with
  `exp(-s₀ log q) = t` and `q^(-s₀) = t`.
- `conditionalPairEpsilonValue_spectralShift`: for bottom-field pairs `A`, `B`
  with zero monodromy and characters `α`, `β` such that the spectral character at
  `s₀` times `α β` is trivial, the pair epsilon value of `(A, B)` at `s` equals
  that of `(α A, β B)` at `s + s₀`. The tensor `A ⊗ B` is equivalent to the
  spectral twist of `αA ⊗ βB` (`tensorTwistCancelEquiv`, the identity map). The
  published `virtual_ofRepresentation` identifies its virtual class with the
  spectral twist of the class. Then the published `virtualTwist_add` combines
  the two spectral twists.
- `restrictTwistEquiv` and `isBaseRestriction_twist`: twisting a bottom-field
  restriction datum of `zM A₀` by `χ ∘ ι` gives a datum of `zM (χ A₀)`.
  `zeroTwistCancelEquiv` with `localUnramifiedCharacter_inv_mul` identifies the
  class of `zM (χ_{z⁻¹} (χ_z A₀))` with that of `zM A₀`.
  `monodromy_eq_zero_of_isBaseRestriction`, with `monodromy_eq_zero_of_equiv`,
  shows that every datum has zero monodromy.
- Existence of data: twist the given data by `χ_z ∘ ι` and `χ_{z'} ∘ ι`. The
  additive character, the measure and the Frobenius are unchanged.
- Every admissible datum `(A', B')` of the twisted classes gives the admissible
  datum `(α A', β B')` of the original classes, with `α = χ_{z⁻¹} ∘ ι` and
  `β = χ_{z'⁻¹} ∘ ι`. The spectral character at `s₀` restricted to the bottom
  subgroup is `(z z') ^ deg`, so the cancellation hypothesis holds. The value at
  `s` is the original value at `s + s₀`, that is `c q^(-m(s + s₀))`.
  `epsilonMonomial_add` rewrites this as `c (z z')^m q^(-ms)`.

The helpers `monodromy_eq_zero_of_equiv`, `tensorTwistMulEquiv`,
`tensorTwistOneEquiv`, `tensorTwistCancelEquiv` and `zeroTwistCancelEquiv` are
stated for an arbitrary field `𝕜` and group `G`.

## Literature

The theorem proved is the derived statement documented in
`HenniartExtensionInputs.md`: Deligne (1973), (3.5.3), PDF p. 29, and
(5.5.1)–(5.5.2), PDF p. 48 (`deligne-1973-local-constants`), as used in Henniart
(1993), §4.4, printed p. 349 (`henniart-1993-epsilon-pairs`). In the Library's
normalization the dependence of epsilon on `s` is already a twist by `|·|^s`, so
the proof needs only the definitions and does not reproduce Deligne's argument.
