# Ordinary smooth duality of twisted block products: proof

Worker 264 wrote the Lean proof and this account of it.

This is internal derived content of the project: it assembles published
Library results on normalized parabolic induction, finite external tensor
products, smooth contragredients and determinant twists. No external literature
result is cited as a proved input.

## Result

`twistedProductOrdinaryDual` has the outer telescope
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)` and
type `TwistedProductOrdinaryDualClause.{uF, uV} F T`, with independent field and
block-carrier universes `uF` and `uV`. So for every
positive rank `n`, block shape `B` of `n`, smooth block family
`δ i : SmoothRep ℂ (GL_{B.size i}(F))` with every `δ i` admissible, and real
exponent family `s`, there is a complex-linear `GL_n(F)`-equivalence

`(i(ν^(s_1) δ_1, …, ν^(s_r) δ_r))~  ≃  i(ν^(-s_1) δ_1~, …, ν^(-s_r) δ_r~)`,

where `~` is the smooth contragredient, `ν = |det|`, and `i(…)` is
`T.twistedProductInduced`: normalized induction from the standard upper block
parabolic of `B`. The blocks, their order and the parabolic are unchanged; the
exponents are negated. No irreducibility, temperedness, unitarity or
finite-dimensionality assumption is added.

## Imports and reused results

- `Parabolic.naturalNormalizedInductionDuality` (module
  `Parabolic.NaturalInductionDualityProof`), whose first component is
  `Parabolic.StandardNaturalInductionDualityClause`: for admissible
  `σ : Rep ℂ (B.Levi F)`, an equivalence
  `(normalizedParabolicInduced B σ)~ ≃ normalizedParabolicInduced B σ~`. Only the
  equivalence is used, not its naturality. The positive half-modulus covariance
  and right-translation construction lie inside that result.
- `FiniteTensor.smoothDualTensorMap` and `smoothDualTensorIntertwiner`
  (`Tensor.SmoothDual`): the canonical map
  `⨂ i, SmoothDual (τ i) → SmoothDual (external τ)` and its intertwining
  property.
- `FiniteTensor.smoothDualTensorInjectivity`
  (`Tensor.SmoothDualInjectivityProof`), used at universes `{0, uF, uV}`:
  `smoothDualTensorMap` is injective for every finite family of
  representations, with no admissibility or cofinality premise.
- `FiniteTensor.smoothDualTensorMap_surjective`
  (`Tensor.SmoothDualSurjectivityProof`): surjectivity for admissible factors
  whose groups have compact open subgroups cofinal among open subgroups; the
  cofinality for `GL_r(F)` is `GeneralLinear.compactOpen_cofinal F T r`
  (`Category.Contragredient`).
- `FiniteTensor.isAdmissible_external` (`Tensor.FiniteProperties`): the external
  tensor of admissible factors is admissible.
- `Langlands.isAdmissible_twist_iff` (`Twist.AdmissibilityProof`) with
  `T.isOpen_ker_determinantPowerCharacter`: twisting by `|det|^s` preserves
  admissibility.
- `smoothContragredientTwistEquiv` (`Twist.SmoothPartDefinitions`): the smooth
  dual of `χ ⊗ ρ` is `χ⁻¹ ⊗ ρ~` on the actual smooth-dual carriers, keeping each
  functional.
- `realPowerCharacter_neg` (`Twist.RealPower`) and `equivOfRepresentationEq`
  (`Category.Twist`).
- `T.normalizedParabolicInducedEquiv` (`Induction.Equivalences`) and
  `T.normalizedProductInducedEquiv` (`Induction.BlockEquivalence`): normalized
  induction carries Levi equivalences, respectively blockwise equivalences, to
  equivalences of induced representations.

## Implemented proof

`segmentFactorSmoothDualEquiv A s` is the equivalence between the smooth dual
of `T.segmentFactor A s = |det|^s ⊗ A` and
`twist (T.determinantPowerCharacter r (-s)) A~`. It composes
`smoothContragredientTwistEquiv` for the character `|det|^s` (its kernel is open
by `T.isOpen_ker_determinantPowerCharacter`) with the identity equivalence
`equivOfRepresentationEq`, using `realPowerCharacter_neg` to rewrite
`(|det|^s)⁻¹` as `|det|^(-s)`. Every functional is kept unchanged.

The main proof fixes the topology of `T` and introduces `n`, `B`, `δ`, `s`, the
admissibility hypothesis and the dual family `δv`. Let `τ i` be the
representation of `T.twistedBlocks B δ s i = ν^(s_i) δ_i`. Each `τ i` is
admissible by `isAdmissible_twist_iff`, so the Levi representation
`σ = B.blockTensor τ` is admissible by `isAdmissible_external`. By definition
`T.twistedProductInduced B δ s` is `normalizedParabolicInduced B σ`, so the
first component of `naturalNormalizedInductionDuality` gives

`E1 : (normalizedParabolicInduced B σ)~ ≃ normalizedParabolicInduced B σ~`.

The map `smoothDualTensorMap τ` is bijective: injective by
`smoothDualTensorInjectivity` applied to the index type `Fin B.length`, and
surjective by `smoothDualTensorMap_surjective` with the cofinality of compact
open subgroups of each `GL_{B.size i}(F)`. With `smoothDualTensorIntertwiner` it gives a
Levi equivalence `e2 : external (fun i => (τ i)~) ≃ σ~`. Its inverse, induced by
`normalizedParabolicInducedEquiv`, identifies `normalizedParabolicInduced B σ~`
with the normalized upper product of the block duals `(τ i)~`. Finally
`normalizedProductInducedEquiv` applied to the block equivalences
`segmentFactorSmoothDualEquiv (δ i) (s i)` reaches the product of the blocks
`ν^(-s_i) δ_i~`, which is `T.twistedProductInduced B δv (fun i => -s i)` by
definition. The result is the composite of these three equivalences.
