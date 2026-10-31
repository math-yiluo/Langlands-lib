# Classification of trivial field-isogeny pullbacks by the normalized character

Author: Worker 934. This module proves
`Langlands.AbelianScheme.FieldTrivialPullbackCharacterBijectiveStatement`
(module `Langlands.AlgebraicGeometry.Picard.FieldIsogenyKernelDescentStatements`,
unchanged) as `fieldTrivialPullbackCharacterBijective`.

The statement says the following. Let `k` be a field, `f : A ⟶ B` an isogeny of
abelian schemes over `Spec k`, and `T` a scheme over `Spec k`. Then the
normalized character
`trivialHomPullbackClassCharacter f (universalGlobalFunctions A)` is a bijection
from `TrivialHomPullbackClasses f T` onto the characters of `ker(f)_T`.
`TrivialHomPullbackClasses f T` is the type of isomorphism classes of line
bundles on `T ×_S B` with a trivialized pullback along `f_T`.

## Declarations

- `fieldTrivialPullbackCharacterBijective_of_descent hU hE` derives the
  statement from the two descent statements of `UnitCocycleDescentStatements`:
  the uniqueness statement `hU` and the effective statement `hE`. Injectivity is
  `trivialPullbackCharacterInjective_of_uniqueness hU`, applied to
  `S = Spec k`. Surjectivity is
  `trivialHomPullbackClassCharacter_surjective_of_effective` with `hE`.
- `trivialHomPullbackClassCharacter_surjective f hf T` gives surjectivity over
  an arbitrary base `S` with no hypothesis. It applies
  `trivialHomPullbackClassCharacter_surjective_of_effective` to the published
  effective descent theorem
  `Langlands.Scheme.Modules.unitCocycleDescentEffective`.
- `trivialHomPullbackClassCharacter_bijective f hf T` gives bijectivity over an
  arbitrary base `S`. Injectivity is the published
  `trivialPullbackCharacterInjective`, which proves
  `TrivialPullbackCharacterInjectiveStatement` from the published uniqueness
  theorem `unitCocycleDescentUniqueness`. Surjectivity is the previous theorem.
- `fieldTrivialPullbackCharacterBijective` specializes
  `trivialHomPullbackClassCharacter_bijective` to the base `Spec k`. The field
  structure and the universe of `k` are not otherwise used.

The mathematical route is faithfully flat descent of line bundles along the
finite, flat, surjective morphism `f_T`. The kernel character gives a unit
cocycle on the kernel pair of `f_T`. Uniqueness of descent gives injectivity,
and effectivity of descent gives surjectivity. The constructions are explained
in `TrivialPullbackCharacterInjective.md` and
`TrivialPullbackCharacterSurjective.md`.
