# Integrals of periodic functions over powers of `𝔸_K / K`

Author: Worker 1709.

This is internal infrastructure for the proof of
`Langlands.Automorphic.CuspidalUnitaryLocalGenericityStatement`. It has no literature
counterpart beyond standard facts about Haar measure on compact abelian groups. Every result is
proved here, and no hypothesis is assumed. The development is used by `Fourier`, `Columns` and
`WhittakerCoefficient` in the same directory.

## General compact groups

Let `G` and `H` be compact Hausdorff abelian topological groups with their Borel σ-algebras.

- `map_eq_of_surjective` says that a continuous surjective additive homomorphism `f : G →+ H`
  pushes a Haar probability measure on `G` forward to the Haar probability measure on `H`. The
  pushforward is a Haar measure (`Measure.isAddHaarMeasure_map_of_isFiniteMeasure`) and also a
  probability measure, so it is the Haar probability measure
  (`Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure`).
- `integral_comp_surjective` is the corresponding change of variables
  `∫ F(f x) dμ = ∫ F dν` for continuous `F`.
- `measurePreserving_continuousAddEquiv` gives the same result for a topological additive
  isomorphism.
- `continuous_integral_of_continuous_uncurry`: for a compact second-countable `Y` with a finite
  measure and a jointly continuous `F : X → Y → ℂ`, the map `x ↦ ∫ F x y dμ` is continuous. The
  proof composes the curried map `X → C(Y, ℂ)` (compact-open, which is the sup norm) with the
  bounded linear functional "integral".

## Measures on `𝔸_K / K`

For a number field `K`, scoped instances put the Borel σ-algebra on `AdeleQuotient K`. This is
the σ-algebra under which the Library's `adeleQuotientHaar` and `constantTerm` are defined.
Further scoped instances give second countability (from `adeles_secondCountableTopology`) and
the Hausdorff property (the principal adeles form a closed subgroup,
`principalAdeles_isClosed`). Assume `CompactSpace (AdeleQuotient K)`. Then
`torusHaar K ι` is the product measure `Measure.pi` of copies of `adeleQuotientHaar K` over a
finite index type `ι`. It is an additive Haar probability measure.

## Periodic functions and torus integrals

- `torusMk : (ι → 𝔸_K) → (ι → 𝔸_K / K)` is coordinatewise reduction. It is a surjective,
  continuous, additive open quotient map.
- `torusLift` is a chosen coordinatewise lift, obtained from `Function.surjInv`.
- `ratVec k` is the image of `k : ι → K`.
- `IsPeriodic f` means `f (y + ratVec k) = f y` for all `y` and `k`. Then
  `f (torusLift (torusMk y)) = f y`, and continuity of `f` implies continuity of
  `f ∘ torusLift`.
- `PreservesRational φ` says that an additive map `φ : (ι → 𝔸_K) →+ (κ → 𝔸_K)` carries rational
  vectors to rational vectors. Such a map induces `torusMap` on tori, and the induced map is
  continuous and surjective when `φ` is.

The torus integral is `torusIntegral ι f = ∫ f (torusLift t) d(torusHaar K ι)(t)`. For periodic
`f` it is the integral of the induced function on `(𝔸_K / K)^ι`. The module proves:

- `torusIntegral_add_right`: invariance under translation by an arbitrary adelic vector
  (periodic `f`). The translation descends to the torus.
- `torusIntegral_comp`: invariance `∫ f(φ y) = ∫ f`, where `φ` is continuous, surjective and
  preserves rational vectors, and `f` is periodic and continuous. Examples of `φ` are invertible
  rational linear changes of variables and coordinate projections. The proof uses
  `integral_comp_surjective` for `torusMap φ`.
- Linearity: `torusIntegral_const`, `torusIntegral_const_mul`, `torusIntegral_mul_const`,
  `torusIntegral_add` and `torusIntegral_sub`.
- `torusIntegral_comm` (Fubini): two torus integrals of a jointly continuous, separately
  periodic function can be swapped. This is `integral_integral_swap`, with integrability coming
  from continuity on a compact space.
- `continuous_torusIntegral`: the integral of a jointly continuous family of periodic functions
  depends continuously on the parameter. `Prod.map id torusMk` is an open quotient map, so the
  lifted family is continuous.
