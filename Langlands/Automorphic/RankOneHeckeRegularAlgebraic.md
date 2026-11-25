# Regular algebraicity of the automorphic `GL(1)` realization of a Hecke character

Module `Langlands.Automorphic.RankOneHeckeRegularAlgebraic`.
These are internal helper results and cite no source. The module sets `autoImplicit false` and
`backward.isDefEq.respectTransparency false`, and declares the function-space `AddCommGroup`
instances locally.

## Algebraic characters of `ℂˣ` (namespace `RankOneHecke`)

- `complexCharacter_val`: the published `InfinityType.complexCharacter a b` takes the value
  `z^a z̄^b`.
- `exponentData a b : ComplexCharacterData` is the data of `z ↦ z^a z̄^b`, with character
  `InfinityType.complexCharacter a b`, weight `a - b` and exponent `(a + b)/2`. The field
  `character_eq` is the polar identity `z^a z̄^b = |z|^(a+b) (z/|z|)^(a-b)`, which follows from
  `z̄ = |z|²/z`.
- `exponentData_character_apply`: `simp` form of the character.
- `rightDerivative_detCharacter_exponentData`: on `GL_1(ℂ)` the right derivative at `1` of
  `g ↦ (exponentData a b).character (det g)` along `X` is `a X₀₀ + b X̄₀₀`. Near `1` the function
  agrees with `Y ↦ (Y₀₀)^a (conj Y₀₀)^b`, and the product rule gives the derivative.

## The infinitesimal character

- `envelopingCharacter χ` is the algebra character `augmentation ∘ heckeEnvelopingShift 1 χ`
  of the enveloping algebra of `GL_1`, and `infinitesimalCharacter χ` is its restriction to the
  center.
- `envelopingCharacter_envelopingGenerator` and `_realGenerator`: on Lie generators it is the
  (complexified) derivative of `χ ∘ det`, by the published `envelopingShift_generator`.
- `characterModule χ` is `ULift ℂ` with the enveloping algebra acting through
  `envelopingCharacter χ`, and `characterVector χ` is its vector `1`.
- `isRegularAlgebraicCharacter_infinitesimalCharacter χ μ hμ` is a criterion. Suppose the
  derivative of `χ ∘ det` along each real diagonal direction `d` equals
  `diagonalWeight F 1 μ d` for an integral weight `μ`. Then `infinitesimalCharacter χ` is
  regular algebraic in the sense of the published `IsRegularAlgebraicCharacter`. The witness is
  the weight `μ`, which is antitone because `Fin 1` has one element, together with the character
  module and its vector `1`. That vector is nonzero, the diagonal acts through `μ`, the
  condition on upper root directions `E_ij` with `i < j` is vacuous, and the center acts
  through the infinitesimal character.
- `cuspidal_hasInfinitesimalCharacter χ`: the center acts on `(cuspidal χ).realization` through
  `infinitesimalCharacter χ`. The published `heckeDeterminantTwistEquiv_differential` and
  `ConstantFunctions.envelopingAction_scalarEquiv` say that an element `z` acts on the line by
  the scalar `augmentation (heckeEnvelopingShift 1 χ z)`. This proof uses
  `set_option maxHeartbeats 1600000`.
- `cuspidal_isRegularAlgebraic χ μ hμ`: under the criterion's hypothesis,
  `(cuspidal χ).isoClass.IsRegularAlgebraic`.

## Exponents at complex places

- `exponentWeight a b` is the integral weight equal to `a v` at the coordinate of the complex
  place `v`, to `b v` at its conjugate coordinate, and to `0` at real coordinates.
- `characterDifferential_diagonal` takes a totally complex `F` and assumes
  `χ.HasComplexPlaceParameter v (exponentData (a v) (b v))` for every complex `v`. Then the
  derivative of `χ ∘ det` along a diagonal direction is `diagonalWeight F 1 (exponentWeight a b)`.
  The direction splits into its complex-place parts (published `sum_placeLieInclusions`).
  Each part is computed by `characterDifferential_complexPlaceLieInclusion` (module
  `ComplexPlaceParameterHeckeTwist`) and
  `rightDerivative_detCharacter_exponentData`.
- `cuspidal_isRegularAlgebraic_of_exponentData`: under the same hypotheses,
  `(cuspidal χ).isoClass.IsRegularAlgebraic`.
