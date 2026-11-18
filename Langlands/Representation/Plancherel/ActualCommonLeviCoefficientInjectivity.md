# Injectivity of the actual common-Levi coefficient map at irreducible points

Module `Langlands.Representation.Plancherel.ActualCommonLeviCoefficientInjectivity`,
namespace `Langlands.Plancherel.ActualCommonLeviV3`. It imports the supporting
module `CoefficientTensorInjectivity` (paired Markdown in the same directory).

## Statements

The setting is that of `ActualCommonLeviV3Statement`: a nonarchimedean local
field `F`, an affine locally finite type group scheme `G` with
`hG : IsConnectedReductive G`, the common Levi `levi χ`, a cocharacter `ψ`
with the same actual dynamic centralizer (`hψ`), a compact open subgroup `K`
with the actual Iwasawa factorization `hψK`, and the inducing `SmoothRep` `A`,
square integrable modulo the central subgroup `C` with the given quotient
Haar measure (`hsq`).

- `unitaryNormalizedInduction χ A ψ hψ z` abbreviates the actual normalized
  induction `(normalizedInductionFunctor (commonDecomposition χ ψ hψ)
  (radical_isClosed ψ)).obj (twistObject χ (unitaryParameter χ z) A)`. Here
  `z` is a unitary unramified parameter.
- `coefficientMap_injective_of_isIrreducible`: if this normalized induction
  is irreducible at `z`, then the actual coefficient map
  `ActualCommonLeviV3.coefficientMap χ hG A C hC qMeasure hsq K hK ψ hψ hψK z`
  of the V.3.1 target is injective.

## Provenance

This is an internal bridge between the published actual coefficient map and
the generic injectivity result. It formalizes no literature statement. It
supports the route of `ActualCommonLeviCoherenceReduction`, which needs dense
coefficient injectivity on unitary parameters.

## Proof

The actual Iwasawa factorization makes the left quotient by `parabolic ψ`
compact (`ActualCommonLeviTensor.quotientCompact`). The unitary twist is
admissible, as the first component of the published
`unitaryTwist_squareIntegrable`. So the normalized induction is admissible by
`Aubert.General.normalizedInductionFunctor_obj_isAdmissible`. Its coefficient
tensor map is injective by `coefficientTensorMap_injective`. By definition
(`CompactInduction.leviCoefficientMap_eq` holds by `rfl`), the actual
coefficient map is that coefficient tensor map composed with the linear
equivalence `CompactInduction.leviCoefficientTensorEquiv` evaluated at the
same data. The composite of an injective map with an equivalence is injective.
