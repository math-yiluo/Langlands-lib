# Forward tensors with the inverse reverse dual operator

This is an internal algebraic helper for Waldspurger, *La formule de Plancherel
pour les groupes p-adiques*, V.3, formula (1), printed p. 295 / PDF p. 61
(registered source `waldspurger-2003-plancherel`).

The inputs `J` and `R` are explicitly supplied intertwiners between the actual
positive-Levi normalized induced representations. `J` goes forward from the
first parabolic to the second; `R` goes in reverse on the representations
induced from the actual smooth contragredients. The inducing Levi subgroups
may differ and their carrier universes are independent.

`reverseInducedDualInverse` uses `Representation.IntertwiningMap.ofBijective R hR`
and its inverse. It therefore inverts the supplied reverse operator itself.
The two inverse identities prove this characterization.
`reverseDualTensorIntertwiner` is `J` tensor that inverse with the external
`G × G` actions. `reverseDualTensorComparison` transfers it to the actual
`leviProductInducedCoefficientObject` carriers using the existing product tensor
equivalences. The pure tensor, original function evaluation and action
formulas follow from the tensor map and those actual comparisons. If the
forward operator is also bijective, bijectivity of the tensor follows from
`TensorProduct.congr`, composed with the product tensor equivalences.

`reverseInducedDual_rescale_bijective` proves that a nonzero scalar multiple
of the particular reverse operator is still bijective, by composing with
`LinearEquiv.smulOfNeZero`. Applying the injective rescaled operator to both
sides proves `reverseInducedDualInverse_rescale`: its inverse is rescaled by
the reciprocal scalar. `reverseDualTensorIntertwiner_rescale` then cancels
the forward and inverse scalars on pure tensors using
`TensorProduct.smul_tmul_smul`; tensor extensionality gives equality on the
whole tensor space. `reverseDualTensorComparison_rescale` transfers this
equality through the same product comparisons. These are algebraic common
scalar cancellation laws, not invariance under independently chosen scalars.

The subgroup hypotheses are the two displayed semidirect decompositions and
closed radicals, local compactness and the nonarchimedean topology. Transferring
to product coefficients additionally uses second countability, the displayed
radical unimodularity and compactness of the two actual left quotients.
No irreducibility hypothesis is used.

This helper has no continuation data or character parameter. In particular,
it does not identify `J` and `R` with the continued standard integrals, prove
a nonempty generic locus, or assert unitary regularity or coefficient/form
preservation. Those applications require the actual common-Levi family
adapter (`ActualCommonLeviTensor`, which applies this helper) and the subsequent
closed targets. The bijectivity witness for `R` is an explicit local algebraic
input here, not a permanent structural hypothesis of the closed extension targets.
