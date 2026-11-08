# Brauer relations among unramified twists over unramified extensions

Author: Worker 1838. This is a supporting unit for task
`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`, which must prove
`Langlands.LocalFactor.NonabelianBrauer.KernelCompatibilityStatement`. It proves the
kernel identity for one special class of actual relations: those in which every
generator lives over an extension with the base absolute ramification index, and
has two unramified twists of one common character with a common exponent. In the
global isolation argument (Deligne 1973, §4.12 and Lemma 4.15) this is the
contribution of the places where the global extension and the characters are
unramified, except for one common twist. It does not prove the general kernel
statement.

## Declarations (`Langlands.LocalFactor.NonabelianBrauer`)

- `baseUniformizer F E L h` is the Library's chosen uniformizer
  `PadicAbelian.uniformizerUnit (fieldData F E)` of `E`, mapped into `L` by the
  actual field inclusion.
- `ord_baseUniformizer`: if `(fieldData F L).ramificationIndex` equals
  `(fieldData F E).ramificationIndex`, this image has order one in `L`. The
  published `LocalClassField.ramificationIndex_mul_ord_relative_algebraMap` gives
  `e_E · ord_L(ι x) = e_L · ord_E(x)` for the inclusion algebra on the two
  `asPadicField` realizations. Cancel the positive index.
- `generatorValue_of_unramifiedTwist`: let a generator `g = (L, χ₀ β, χ₀' β)` have
  `χ₀`, `χ₀'` unramified and `L` of the base ramification index. Then its abelian
  epsilon ratio for `ψ ∘ Tr_{L/E}` is the character ratio of `g` at the uniformizer
  of `E`, raised to `n(ψ ∘ Tr_{L/E}) + a(β)`. The proof applies the published
  `abelianEpsilonExpression_mul_unramified` (Deligne's (3.4.3.5)) to `β` twisted
  by `χ₀` and by `χ₀'`. `abelianUnramifiedTwistFactor_eq_uniformizer` evaluates both
  twisting factors at `baseUniformizer`, and the common factor `ε(β)` cancels.
  The character ratio of the generator is `χ₀(π)/χ₀'(π)` because `β(π)` cancels.
- `evaluationMap_eq_zero_of_unramifiedTwist`: let `presentationMap F e E z = 0` for
  a normalized reciprocity family. Suppose every support generator has the above
  form with the same exponent `N`. Then `evaluationMap F E ψ measures z = 0`. Each
  generator value is the `N`-th power of its character ratio at the uniformizer of
  `E`. So the evaluation is `N` times the character-ratio evaluation of the
  published `BrauerKernel.Determinant` module, and that vanishes on actual
  relations by `characterRatioMap_eq_zero` (Gallagher's determinant formula with
  the transfer/inclusion square).

The Haar family is arbitrary and unchanged. The field universe `uF` and the
representation universe `uV` are independent.

## Scope

The hypothesis that `n(ψ ∘ Tr) + a(β)` is the same for every generator is explicit.
When the generator fields are unramified over `E` and `β` is the norm pullback of
one character of `E`, it follows from `n(ψ ∘ Tr_{L/E}) = n(ψ)` and
`a(α ∘ N_{L/E}) = a(α)`. Those two facts are a separate unit.

## Provenance

Deligne, *Les constantes des équations fonctionnelles des fonctions L* (1973),
registered as `deligne-1973-local-constants`, SHA256
`b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`: Lemma 4.15
(printed page 545, PDF page 45), the existence of a constant theory for unramified
data, and formula (3.4.3.5) (printed page 528, PDF page 28) for unramified twists.
This module is an internal derivation of the corresponding relation-level
statement from published Library theorems.
