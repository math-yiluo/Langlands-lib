# Product induction with the positive Levi normalization

This derived construction transports the actual normalized product-induction
equivalence to the positive Levi-twist-before-inflation model of Waldspurger I.3.
It retains explicit closed radical unimodularity assumptions. The product
radical's unimodularity is derived from the two factor assumptions using the
actual product Haar modulus. The equivalence is equivariant and preserves
pointwise pure tensor values; a commuting square compares it with the existing
full-parabolic product equivalence.

The source is J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques (d'après Harish-Chandra)*, DOI 10.1017/S1474748003000082,
I.3, printed p.243 (PDF p.9), and V.1, printed p.288 (PDF p.54).
The registered source is `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
I.3 fixes positive Levi covariance and uniform open right invariance.
V.1 uses induction from the actual product parabolic in its definition of
`L(ω,P)` and identifies it with the tensor of two inductions. The present
transport and product unimodularity arguments are internal derived adapters,
rather than additional assertions attributed to the source.

## Inputs and scope

The independent ambient groups are locally compact nonarchimedean topological
groups `G : Type uG`, `H : Type uH`. Actual subgroups have semidirect
decompositions `h : IsSemidirectDecomposition P M U` and
`k : IsSemidirectDecomposition Q N V`. Both radicals are closed and satisfy
`IsUnimodularModulus`, meaning that each inner conjugation has Haar modulus one.
The objects `A : SmoothRep ℂ M`, `B : SmoothRep ℂ N` have independent carrier
universes `uV`, `uW`.

The external normalization comparison needs no countability or quotient
compactness. The product unimodularity lemma and the main equivalence use
`SecondCountableTopology` on both groups for the product Haar identity.
The main equivalence additionally uses compactness of the actual left quotients
`Induction.LeftQuotient P` and `Induction.LeftQuotient Q`, as required by the
existing product-induction equivalence.

The setting is broader than the source's admissible representations of reductive
rational-point groups. No admissibility conclusion is claimed. Actual rational
realizations retain their structural and topological obligations. No analytic
coefficient, duality, Hermitian-form or Plancherel conclusion is claimed here.

## Construction

`isUnimodularModulus_prod` specializes
`HaarModulus.closedRestrictCharacter_prod` to the factor radicals themselves.
The two inner moduli are one by the factor hypotheses, so their product is one.
The normalizer-character and restricted-character expressions agree by their
definitions and proof irrelevance.

`externalInductionLeviEquiv` pulls the existing
`normalizedInductionLeviEquiv` along the two coordinate projections, then
applies `FiniteTensorFiltration.tprodCongr`. Thus it is an actual representation
equivalence on `G × H`, with linear map the tensor of the two normalization
maps. Its forward and inverse pure tensor formulas follow from
`TensorProduct.congr`.

`leviNormalizedProductInductionTensorEquiv` composes the inverse external
normalization comparison, the published
`normalizedProductInductionTensorEquiv`, and the product instance of
`normalizedInductionLeviEquiv`. The last component uses the derived product
unimodularity proof, not an additional hypothesis.

`leviNormalizedProductInductionTensorEquiv_commutes` cancels the external
comparison with its inverse. It states equality for every tensor, so the
comparison square includes arbitrary finite sums.

`leviNormalizedProductInductionTensorEquiv_tmul_eval` uses the inverse factor
formula, the existing full-parabolic product evaluation formula, and the
value-preservation formulas of the three normalization comparisons. At
`x : G × H` it gives `f(x.1) ⊗ j(x.2)`, on the actual source-normalized
induced function space.
