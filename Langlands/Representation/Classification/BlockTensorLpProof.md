# The common finite-exponent comparison for actual GL block tensors

Author: Worker 450.

`Langlands.glBlockTensorLp` proves the complete published proposition
`Langlands.GLBlockTensorLpStatement.{uF, uV}` from
[BlockTensorLpStatement](BlockTensorLpStatement.md). Its type has no outer
arguments or additional premises. The field universe `uF` and representation
carrier universe `uV` are independent, in that order.

For every real `r ≥ 2`, every supplied compatible p-adic topology `T`, every
positive total rank and block shape `B`, and every family of irreducible
admissible actual GL block representations `ρ i`, the theorem proves

```text
(∀ i, T.IsLp (ρ i) r) ↔
  ∀ Borel realizations on B.Levi F.Carrier / its full center,
    ∀ Haar measures μ, IsLpModCenter (B.blockTensor ρ) μ r.
```

All coefficients use the entire actual smooth dual and the entire algebraic
tensor carrier. The target's all-open admissibility and irreducibility premises,
its specified group topologies, and every measurable-space and measure
quantifier are retained. Factor Haar measures chosen inside the proof are local
tools. The closed conclusion contains neither a chosen normalization nor a
chosen central character.

## Published inputs and provenance

This is an internal proof of the derived common proposition, whose conventions
and relation to the two final analytic targets are documented in the unchanged
[BlockTensorAnalyticStatement](BlockTensorAnalyticStatement.md). No external
literature theorem is newly cited as proving this finite-product comparison.
The implemented argument assembles the following published constructions and
proofs, imported by Lean name.

| Published input | Role here |
| --- | --- |
| `Group.Center.quotientPiContinuousMulEquiv` and `quotientPiMeasurableEquiv` in `Group/Center/FiniteProduct` | Identify the quotient by the full product center with the actual product of factor central quotients, with the existing topologies and Borel realizations. |
| `FiniteTensor.externalUnitaryCentralCharacter` and `restrictUnitaryCentralCharacter` in `Tensor/UnitaryCentralCharacter` | Assemble factor character witnesses and recover factor witnesses from a tensor witness; restriction uses nontrivial carriers. |
| `FiniteTensor.smoothDualTensorMap` and `matrixCoefficient_smoothDualTensorMap_tprod` in `Tensor/SmoothDual` | Supply the actual smooth-functional tensor map and the pure coefficient identity. |
| `FiniteTensor.smoothDualTensorSurjectivity` in `Tensor/SmoothDualSurjectivityProof` | Express every smooth tensor functional as the image of a tensor of smooth factor functionals, using admissibility and compact-open cofinality. |
| `FiniteTensor.isSmooth_external` and `isAdmissible_external` | Supply smoothness and all-open admissibility of the actual external tensor. |
| `UnitaryCentralCharacter.continuous_coefficientNorm` and `aestronglyMeasurable_coefficientNorm` in `MatrixCoefficient/NormRegularityProof` | Give continuity and measurability of descended coefficient norms for smooth vectors. |
| `smoothBidual_injective_of_compact_cofinal` in `Smooth/Contragredient/AdmissibleDualityProof` | Supply separation of nonzero vectors by actual smooth functionals. |
| `glBlockCentralQuotientTopology` in `Group/GL/CentralQuotientTopologyProof` | Supply local compactness, second countability, Haar existence and sigma-finiteness on the actual factor and Levi central quotients. |
| `T.generalLinearCompactOpen` in `Group/GL/CompactOpen` | Place a compact open subgroup inside each open factor subgroup. |
| `haarMemLpInvariant` in `Analysis/HaarLpProof` | Compare arbitrary Haar normalizations on a fixed Borel realization. |
| `finiteProductMemLpPreservation` and `finiteProductMemLpNonzeroIff` in `Analysis/FiniteProductLpProof` | Preserve membership for separated products, including zero factors, and reflect it when every factor is not almost everywhere zero. |

The remaining measure operations are from the pinned Mathlib environment:
Haar transport under a continuous multiplicative equivalence, Haar product
measures, `MeasurableEquiv.memLp_map_measure_iff`, the continuous-function
`ae_eq_iff_eq` criterion for measures positive on open sets, and the addition,
domination and scalar multiplication rules for `MemLp`.

## Coefficients and Haar transport

`FiniteTensor.coefficientNorm_smoothDualTensorMap_tprod` proves that the
actual descended norm of a pure tensor coefficient becomes the product of
factor norms under `quotientPiMulEquiv`. Quotient induction reduces the identity
to `matrixCoefficient_smoothDualTensorMap_tprod` and multiplicativity of the
complex norm. The factor and tensor character witnesses can be arbitrary:
evaluation on a quotient representative is the absolute matrix coefficient
for either witness. The companion `_comp` theorem states this identity after
composition with the inverse continuous quotient equivalence.

`Group.Center.memLp_quotientPi_iff` compares an arbitrary Haar measure `μ` on
the full product central quotient with the image of `Measure.pi ν` under that
inverse equivalence. The product of the sigma-finite factor Haar measures is
Haar, and the continuous multiplicative equivalence transports it to a Haar
measure. `haarMemLpInvariant` compares this measure with `μ`. The measurable
equivalence then transfers membership to `Measure.pi ν`. Second countability
of the factors supplies the Borel compatibility for their finite product.

`isLpModCenter_iff_haar` applies the same normalization invariance to every
coefficient while retaining its admissibility and central-character witness.
It works within any supplied Borel realization of a locally compact,
second-countable central quotient.

The four `UnitaryCentralCharacter.memLp_coefficientNorm_*` helpers establish
closure under addition and complex scalar multiplication in either argument.
For addition the pointwise norm triangle inequality on quotient representatives
and continuity give `MemLp.mono'` applied to a sum of integrable functions.
Scaling multiplies the real descended norm by the scalar's norm, so
`MemLp.const_smul` applies. Two `PiTensorProduct.induction_on` arguments in
`FiniteTensor.memLp_coefficientNorm_smoothDualTensorMap` extend pure membership
to every vector tensor and every functional in the canonical map's image.

## Generic preservation and reflection

The private `FiniteTensor.isLpModCenter_external_iff` assembles the argument
for a nonempty finite family of nontrivial admissible factors. Its explicit
map-surjectivity input is discharged in the GL specialization below.

For preservation, choose character witnesses from the factor predicates and
assemble `externalUnitaryCentralCharacter`. Product integration gives membership
for every pure coefficient after the quotient/Haar transport. The two tensor
inductions give membership for every vector and every functional in the map's
image. Surjectivity covers every actual smooth functional. Tensor admissibility
is `isAdmissible_external` applied to the factor hypotheses.

For reflection, restrict the tensor character to each factor. Fix a tested
smooth coefficient in factor `i`. If its descended norm is almost everywhere
zero, `MemLp.zero` and a.e. congruence give membership immediately. Otherwise,
choose smooth auxiliary coefficients nonzero at the identity in every other
factor. The module's `exists_smoothDual_pairing_ne_zero_of_ne_zero` proves
smooth separation from injectivity of the published smooth bidual map; choosing
a nonzero vector gives `exists_smooth_coefficient_ne_zero`.

`UnitaryCentralCharacter.coefficientNorm_not_ae_zero` shows that each auxiliary
norm is not almost everywhere zero for Haar measure. A hypothetical a.e. zero
identity between continuous functions would hold everywhere, because Haar
measure is positive on nonempty open sets. Evaluation at the identity would
contradict the chosen nonzero pairing. Update the auxiliary family in coordinate
`i` with the tested coefficient. Every resulting factor is a.e. strongly
measurable and not a.e. zero. The tensor predicate gives membership of their
pure product coefficient, and quotient/Haar transport gives membership of the
separated product. `finiteProductMemLpNonzeroIff` then recovers membership of
the tested factor without assuming any auxiliary factor integrable.

The imported reflection theorem uses the extended nonnegative Tonelli integral
of the power of each norm. Each factor integral is nonzero, and finiteness of
their product forces every factor integral to be finite. This supplies the
reflection step directly; no restriction of an `Lp` class to a coordinate
slice is made.

## The exact GL specialization

The private `glBlockTensorLp_of_smoothDualSurjectivity` has conclusion exactly
`GLBlockTensorLpStatement.{uF, uV}`. It introduces the published telescope and
installs precisely `T.topology` and `T.leviTopology B`. Positive total rank gives
a block index via `B.indexEquiv.symm` applied to the zero coordinate of `Fin n`.
Factor irreducibility gives nontrivial carriers. The published quotient topology
proof supplies all the factor and Levi quotient properties used above.

The factor measurable spaces are exactly
`T.centralQuotientMeasurableSpace (B.size i)`, with their published Borel proofs.
Choose a Haar measure on each of these actual quotients and obtain its
sigma-finiteness. Applying `T.generalLinearCompactOpen` to an open subgroup as
an identity neighborhood proves compact-open cofinality. The supplied
surjectivity proposition then applies to the actual GL family and its
all-open admissibility hypotheses.

In the forward implication, apply the generic comparison for every Borel
realization and every Haar measure supplied on the Levi quotient. For the
reverse implication, choose the Borel sigma algebra of that actual quotient
and one Haar measure, whose existence is proved by the topology input. The
assumed all-realizations predicate gives the tensor condition for this measure.
Generic reflection yields the factor predicates for the local factor measures;
`isLpModCenter_iff_haar` supplies every canonical factor Haar normalization.

Finally, `glBlockTensorLp` applies this wrapper to the published closed theorem
`FiniteTensor.smoothDualTensorSurjectivity.{0, uF, uV}`. Thus no surjectivity
hypothesis remains in the closing declaration. The index universe alone is
specialized to zero. The real bound `r ≥ 2` supplies `0 < r` for product
integration. No topology or countability is imposed on the representation
carriers. The only axioms used are `propext`, `Classical.choice` and `Quot.sound`.

The statement pair, the analytic statement pair and all their imported pairs
are unchanged. The square-integrability and temperedness specializations remain
separate consumers of this common result.
