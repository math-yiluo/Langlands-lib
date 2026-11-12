# Arithmetic pullback of actual automorphic operator realizations

This module is an internal construction. It generalizes the published CM
modules `CMOperatorConjugation`, `StableAutomorphicCMTransport` and
`OperatorCMTransport` from the CM involution to an arbitrary number-field
isomorphism `e : K ≃+* L`, with `K`, `L` and `M` in independent universes and
any rank `n`. Together with `ArithmeticTransportRelation`, it constructs the
arithmetic transport of every actual realization. That relation module states
transport only as a relation between realizations that are given. No new object
from the original literature is identified here.

## A general order isomorphism

`Langlands.covariantSubrepresentationOrderIso ρ τ α e hc` takes:

- representations `ρ` of a monoid `G` on `V` and `τ` of a monoid `H` on `W`;
- a monoid isomorphism `α : H ≃* G`;
- a complex linear equivalence `e : V ≃ₗ[ℂ] W` with `τ h (e f) = e (ρ (α h) f)`.

It returns the order isomorphism between invariant subspaces given by image
and preimage under `e`. The published `conjugatedSubrepresentationOrderIso`
requires `G = H`, so it cannot compare operator algebras of two different
fields. The published `FiniteLocalCMTransport` has a private version of the
same construction, which other modules cannot use.

## Operators

Write `Φ = finiteSmoothEquiv n e`: pullback of real-smooth functions with a
common open finite stabilizer from `GL_n(𝔸_L)` to `GL_n(𝔸_K)`.

- `finiteSmoothEquiv_finiteRightAction` and
  `finiteSmoothEquiv_compactRightAction`: `Φ` carries translation by
  `finiteEquiv n e d`, respectively by
  `ArchimedeanCompactTransport.compactEquiv n e k`, to translation by `d`,
  respectively `k`.
- `finiteSmoothArithmeticConjugation n e` is `a ↦ Φ ∘ a ∘ Φ⁻¹`, an algebra
  isomorphism of the full endomorphism algebras. It is Mathlib's
  `LinearEquiv.conjAlgEquiv`. Its inverse is the conjugation for `e.symm`
  (`finiteSmoothArithmeticConjugation_symm`).
- The lemmas `finiteSmoothArithmeticConjugation_finite`, `_compact` and
  `_differential` compute it on the three generator families. Translation by
  `d`, by `k`, and the enveloping element `u` over `L` go to translation by
  `(finiteEquiv n e).symm d`, by `(compactEquiv n e).symm k`, and the element
  `(envelopingEquiv n e).symm u` over `K`.
- Induction over `Algebra.adjoin` shows that it maps the concrete operator
  algebra `automorphicOperatorAlgebra L n` into `automorphicOperatorAlgebra K n`.
  `operatorArithmeticConjugation n e` is the resulting algebra isomorphism of
  operator algebras. Its simp lemmas evaluate it on `finiteOperator`,
  `compactOperator` and `differentialOperator`.
- `operatorAction_finiteSmoothEquiv` is whole-algebra covariance:
  `(conj a) (Φ f) = Φ (a f)`.

## Stable cores

`automorphicOperatorCore` is the largest operator-invariant subspace of the
automorphic forms.

- `mem_automorphicOperatorCore_finiteSmoothEquiv` and
  `finiteSmoothEquiv_mem_automorphicOperatorCore_iff`: `Φ` preserves and
  reflects membership in the core. Covariance moves every operator over `K`
  back to an operator over `L`, and `Φ` preserves automorphic forms.
- `StableAutomorphicFunctions.arithmeticEquiv n e` is the restricted continuous
  linear equivalence.
  - Identity, composition and inverse laws: `arithmeticEquiv_refl`,
    `arithmeticEquiv_trans` and `arithmeticEquiv_symm`.
  - Whole-algebra covariance in both directions:
    `operatorAction_arithmeticEquiv` and `operatorAction_arithmeticEquiv_symm`.
  - The three generator covariances: `finiteAction_arithmeticEquiv`,
    `compactAction_arithmeticEquiv` and `envelopingAction_arithmeticEquiv`.
  - The inclusion into forms (`inclusion_arithmeticEquiv`) and evaluation
    (`evaluate_arithmeticEquiv`).

## Realizations

`OperatorRealization F n` is an invariant subspace of the stable core.

- `OperatorRealization.arithmeticComapOrderIso e` is the order isomorphism of
  realizations over `L` and over `K`. It is induced by the stable-core
  equivalence and the inverse operator conjugation.
- `S.arithmeticComap e` is the image of `S`. Its `toSubmodule` is the image
  submodule.
  - `arithmeticComap_refl`, `arithmeticComap_trans` and the two inverse laws
    hold as equalities of realizations.
- `S.arithmeticComapEquiv e : S.Space ≃L[ℂ] (S.arithmeticComap e).Space`
  restricts the pullback.
  - `arithmeticComapEquiv_operatorAction`, `_finite`, `_compact` and
    `_differential` give the covariance of all operators. The `_symm_` variants
    state it for the inverse.
  - The form inclusion and the underlying continuous function of the image of
    `f` are the pullbacks of those of `f` (`formInclusion_arithmeticComapEquiv`,
    `toContinuous_arithmeticComapEquiv`, `evaluate_arithmeticComapEquiv`).

Results:

- `isArithmeticTransport_arithmeticComap`:
  `IsArithmeticTransport e (S.arithmeticComap e) S`. The pulled-back
  realization over `K` is transported to `S` along `e`. The witness is the
  inverse of `arithmeticComapEquiv`.
- `exists_isArithmeticTransport`: every realization `T` over `K` has an actual
  transport over `L`, namely `T.arithmeticComap e.symm`. This answers the
  existence question left open in `ArithmeticTransportRelation`.
- `isArithmeticTransport_iff`: `IsArithmeticTransport e T S` holds exactly when
  `T` is fully equivalent to `S.arithmeticComap e`.
- `arithmeticComapSubrepresentationOrderIso` and
  `arithmeticComap_isIrreducible_iff`: invariant subspaces correspond, so
  irreducibility for the whole operator algebra is preserved and reflected.
- `arithmeticComap_hasCentralCharacter_iff`: central character `χ` corresponds
  to `HeckeCharacter.comap e χ`.
- `arithmeticComap_isCuspidal_iff`: cuspidality is preserved and reflected.
  This needs the compactness parameters of both adele quotients.

`CuspidalOperatorRealization.arithmeticComap e` packages the image of an
actual irreducible cuspidal realization of rank `r + 1` with these proofs. It
satisfies:

- the two inverse laws;
- `arithmeticComap_hasCentralCharacter_iff`;
- `isArithmeticTransport_arithmeticComap`.

## Scope and conventions

Pullback along `e : K ≃+* L` goes from objects over `L` to objects over `K`, as
in the published arithmetic modules. So the transport along `e` of a
realization `T` over `K` is `T.arithmeticComap e.symm`. For a Galois
automorphism `σ`, the conjugate `c ∘ σ⁻¹` is pullback along `σ⁻¹`.
`OperatorArithmeticTransportClasses` packages this on classes. All
coefficients are complex. No topology is put on the realizations beyond the
inherited one. Local components, tensor factorization, multiplicities and
spectral existence are not addressed.
