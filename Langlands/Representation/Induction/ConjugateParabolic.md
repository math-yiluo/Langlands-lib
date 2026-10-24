# Normalized induction from actual conjugate block parabolics

Author: Worker 264. Worker 19 specified the downstream use and the required
interface. The p-adic wrapper follows the published upper parabolic wrapper in
`Induction/Parabolic` and its opposite-parabolic adaptation.

A concrete pair `P : Exponents.ConjugateBlockPair n R` consists of a block shape
`B = P.shape` and a conjugator `c = P.conjugator`. Its actual parabolic
`P.parabolic` is the image of `B.parabolic R` under `MulAut.conj c`, that is
`c * B.parabolic R * c⁻¹`. This module constructs, in order:

1. coordinate transport between `B.parabolic R` and `P.parabolic`, together with
   the actual conjugate Levi embedding and projection;
2. normalized smooth induction from `P.parabolic` along that projection;
3. a representation equivalence from standard normalized parabolic induction to
   this induction, given by left translation by `c⁻¹`.

Rank zero is included because `n` is arbitrary: with `n = 0` and the empty
block shape, every construction and law below applies unchanged.

## Generic conjugate-subgroup helper

In `Langlands.Induction`, let `G` be any topological group, `P Q` subgroups,
`σ`, `τ` representations of `P` and `Q` on one module `V`, and `e : P ≃* Q`
with `(e p : G) = c * p * c⁻¹` and `τ (e p) = σ p`. Then:

- `translateSmoothFunction a e he hστ f` is the function `x ↦ f (a * x)`, for
  `(e p : G) = a⁻¹ * p * a`. Its covariance comes from `a * (a⁻¹ p a x) =
  p (a x)` and the covariance of `f`. The same open subgroup stabilizes it,
  because left and right translations commute.
  `translateSmoothFunction_eval` and `translateSmoothFunction_stabilizer`
  record these facts.
- `conjugateSmoothInducedEquiv c e he hστ` is an actual
  `(smoothInduced P σ).Equiv (smoothInduced Q τ)`. Its forward map is the
  translate by `a = c⁻¹`, with evaluation `f ↦ (x ↦ f (c⁻¹ * x))`
  (`conjugateSmoothInducedEquiv_eval`). Its inverse is the translate by
  `a = c` for `e.symm`, with evaluation `h ↦ (x ↦ h (c * x))`
  (`conjugateSmoothInducedEquiv_symm_eval`). Linearity is pointwise and
  definitional. The two inverse identities reduce to `c⁻¹ (c x) = x` and
  `c (c⁻¹ x) = x`. Intertwining for the ambient right-translation action
  reduces to `c⁻¹ x g = c⁻¹ (x g)`.
- `conjugateSmoothInducedEquiv_stabilizer_iff` proves that, for every open
  subgroup `K`, the transported function is right `K`-invariant if and only if
  the original function is.
- `conjugateSmoothInducedEquiv_naturality` proves that the equivalence commutes
  with `smoothInducedMap` of intertwiners `φ`, `ψ` that have the same
  underlying linear map.

## Conjugate block geometry

In `Langlands.Exponents.ConjugateBlockPair`, for any commutative ring `R`:

- `mem_parabolic_iff`: `g ∈ P.parabolic ↔ c⁻¹ * g * c ∈ B.parabolic R`.
- `parabolicEquiv : B.parabolic R ≃* P.parabolic` sends `p` to
  `c * p * c⁻¹`; its inverse sends `q` to `c⁻¹ * q * c`
  (`parabolicEquiv_apply`, `parabolicEquiv_symm_apply`, both definitional).
- `leviEmbedding : B.Levi R →* GeneralLinear n R` is
  `m ↦ c * B.leviEmbedding R m * c⁻¹` (`leviEmbedding_apply`), and it is
  injective (`leviEmbedding_injective`). `leviInParabolic` is the same
  embedding, valued in `P.parabolic` (`leviInParabolic_val`).
- `leviProjection : P.parabolic →* B.Levi R` applies the published
  `B.leviProjection R` to `c⁻¹ * q * c` (`leviProjection_apply`).
  `leviProjection_parabolicEquiv` proves that it restricts along
  `parabolicEquiv` to the standard projection. `leviProjection_section` proves
  the section/projection identity `P.leviProjection (P.leviInParabolic m) = m`
  from the published standard identity.
- `leviSubgroup` is defined as the range of `P.leviEmbedding`; it is not an
  arbitrary supplied subgroup. `leviSubgroup_le_parabolic` proves that it lies
  in `P.parabolic`.

For a topological commutative ring `R`, the following are continuous.
`parabolicEquivContinuous` is a topological group isomorphism; both directions
are continuous because multiplication by constants is. `leviEmbeddingContinuous`
composes the published continuous standard embedding with conjugation.
`leviProjectionContinuous` composes the published continuous standard
projection with the continuous inverse of `parabolicEquivContinuous`.
`leviInParabolicContinuous` is the embedding corestricted to the subgroup
topology.

## Induction for a supplied Levi character

For a topological commutative ring `F`, a smooth character `χ` of `B.Levi F`,
and a representation `σ` of `B.Levi F` on `V`:

- `inflateCharacter χ` is `χ ∘ P.leviProjection`. Its kernel is open, being the
  preimage of the open kernel of `χ` under the continuous projection.
- `inducingRepresentation χ σ` is
  `twist (inflateCharacter χ) (σ.comp P.leviProjection)`.
  `inducingRepresentation_parabolicEquiv` proves that along `parabolicEquiv` it
  equals the published standard `B.inducingRepresentation χ σ`.
- `normalizedInducedOf χ σ` is the published
  `Induction.normalizedSmoothInduced` for `P.parabolic`. It acts on
  `Induction.SmoothFunctions P.parabolic (P.inducingRepresentation χ σ)`, the
  covariant functions with one uniform open right stabilizer each.
  `normalizedInducedOf_covariant` proves
  `f (q * g) = χ (m q) • σ (m q) (f g)`, with `m = P.leviProjection`.
  `normalizedInducedOf_apply` proves `(g · f) x = f (x * g)`, and
  `isSmooth_normalizedInducedOf` proves smoothness.
- `inducingMap` and `normalizedInducedOfMap` send a Levi intertwiner `f` to the
  inflated intertwiner and to postcomposition by `f`. Evaluation, identities and
  composition are `normalizedInducedOfMap_apply`, `_id` and `_comp`.
  `normalizedInductionFunctorOf χ` bundles these as a functor
  `SmoothRep.{0, uF, uV} ℂ (B.Levi F) ⥤ SmoothRep.{0, uF, max uF uV} ℂ
  (GeneralLinear n F)`.
- `conjugateInducedEquiv χ σ : (B.normalizedInducedOf χ σ).Equiv
  (P.normalizedInducedOf χ σ)` is the generic helper applied to
  `parabolicEquiv`. Its lemmas are `_eval` (`f ↦ f (c⁻¹ * x)`), `_symm_eval`
  (`h ↦ h (c * x)`) and `_naturality`. `conjugateInductionIso χ` is the
  corresponding natural isomorphism from `B.normalizedInductionFunctorOf χ` to
  `P.normalizedInductionFunctorOf χ`, with components `SmoothRep.mkIso`.

## The p-adic wrapper

In `Langlands.PadicField.TopologicalData`, for a p-adic realization `T` and a
representation `σ` of `B.Levi F.Carrier` on `V`:

- `T.conjugateParabolicHalfModulus P` is `T.leviHalfModulus B ∘
  P.leviProjection`, the positive half of the published upper block modulus
  transported along the conjugate projection. Its restrictions along
  `parabolicEquiv` and along the Levi section are
  `T.parabolicHalfModulus B` and `T.leviHalfModulus B`
  (`_parabolicEquiv`, `_section`). `isOpen_ker_conjugateParabolicHalfModulus`
  proves that its kernel is open.
- `T.normalizedConjugateParabolicInduced P σ` is `normalizedInducedOf` for the
  published `T.leviHalfCharacter B`. The inducing representation is
  `twist (T.conjugateParabolicHalfModulus P) (σ.comp P.leviProjection)`.
  The following formulas are proved:

  ```
  f (q * x) = (T.leviHalfModulus B (P.leviProjection q) : ℂ) •
                σ (P.leviProjection q) (f x),
  (g · f) x = f (x * g).
  ```

  They are `normalizedConjugateParabolicInduced_covariant` and
  `normalizedConjugateParabolicInduced_apply`. Smoothness is
  `isSmooth_normalizedConjugateParabolicInduced`.
- `T.normalizedConjugateParabolicInducedMap P f` is postcomposition by a Levi
  intertwiner `f`, with `_apply`, `_id` and `_comp`.
  `T.normalizedConjugateParabolicInductionFunctor P` is the bundled functor
  between the canonical smooth categories.
- `T.conjugateParabolicInducedEquiv P σ :
  (T.normalizedParabolicInduced B σ).Equiv
  (T.normalizedConjugateParabolicInduced P σ)` specializes
  `conjugateInducedEquiv`. Its lemmas are:
  - `_eval`: evaluation `f ↦ (x ↦ f (c⁻¹ * x))`;
  - `_symm_eval`: inverse `h ↦ (x ↦ h (c * x))`;
  - `_covariant`: covariance of the transported function;
  - `_symm_apply_apply`, `_apply_symm_apply`: the inverse identities;
  - `_intertwining`: equivariance for the ambient right-translation actions;
  - `_stabilizer_iff`: preservation of each uniform open right stabilizer, in
    both directions;
  - `_naturality`: commutation with the induced maps of Levi intertwiners.

  Linearity is part of the `Representation.Equiv` structure.
  `T.conjugateParabolicInductionIso P` is the natural isomorphism from
  `T.normalizedParabolicInductionFunctor B` to
  `T.normalizedConjugateParabolicInductionFunctor P`.

`F.canonicalNormalizedConjugateParabolicInduced P σ`,
`F.canonicalNormalizedConjugateParabolicInductionFunctor P` and
`F.canonicalConjugateParabolicInducedEquiv P σ` use the published canonical
topological realization of every algebraic p-adic field.

## Universes and topology

For `F : PadicField.{uF} p` and `V : Type uV`, the universes `uF` and `uV` are
independent. The function spaces, and so the induced functor's target
`SmoothRep.{0, uF, max uF uV}`, live in `Type (max uF uV)`. Maps allow further
independent carrier universes `uW` and `uX`. The topology on `F.Carrier` is
`T.topology`, and every group and Levi topology is the published one induced
from it. The topological-ring instance is obtained, as in `Induction/Parabolic`,
from `T`'s valuation and local-field structure.

## Derived provenance and source correspondence

This is a derived construction, not a new representation-theoretic theorem.
It composes the accepted `Exponents/ParabolicPair`, `Group/GL/Blocks` with its
block topology, `Group/GL/BlockModulus`, `Twist/Definitions`,
`Induction/Definitions`, `Induction/Parabolic` and `Category/Basic`. The
conjugate inducing data are defined by transport along conjugation by `c`. The
only new mathematical input is the elementary fact that left translation by
`c⁻¹` carries `B.parabolic`-covariant functions to `c B c⁻¹`-covariant
functions and commutes with right translation.

The normalizing scalar is the transported positive half of the published
upper determinant block modulus. Its identification with a Haar module for the
conjugate parabolic is neither assumed nor proved here.
`Exponents.WeakCritical.pullbackRep`, which transports a representation by
inner conjugation, is a different construction and is not used.

A. J. Silberger, *The Langlands quotient theorem for p-adic groups* (1978),
Corollary 6.2 and its proof, printed page 103 / PDF page 9. The proof chooses
`y` such that `(P^y, A^y)` is a standard p-pair and uses that the
representation induced from the semistandard parabolic is equivalent to the
representation induced from the standard one. This module supplies that
conjugate-induction step for block parabolics of general linear groups, as an
explicit left-translation equivalence. It asserts neither the uniqueness
conclusion of Corollary 6.2, nor Proposition 6.1, nor the existence of a Weyl
representative `y` normalizing a semistandard pair to a standard one. Those
remain separate obligations. The cited page was read directly.

Registered source:

- `provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
  SHA256 `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`,
  Corollary 6.2 and its proof, printed page 103 / PDF page 9 (downstream use).

No compact-induction variant is constructed. Admissibility, irreducibility,
Langlands classification and quotient existence are not asserted.
