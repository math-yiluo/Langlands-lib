# Norms of pure compact tensors in the common-Levi comparison

`compactFormalDegreeModel_norm_tmul` computes the norm of a pure tensor in
`compactFormalDegreeModel`. The evaluation of `compactProductTensorEquiv`
on such a tensor is pointwise evaluation of both sections. The exact integral
formula of `formalDegreeFixedProductCompactForm_inner_integral` then factors
by `coefficientTensorInvariantForm_inner_tmul` and `integral_prod_mul`. This
uses the same compact probability measure in both factors and the original
formal degree for the prescribed central quotient measure.

`compactComparison_norm_eq` transports `genericComparison_preserves_unitary`
through `compactComparison_square` and `compactFormalDegreeModel_inner`.
These facts express the compact probability norm comparison used in the proof
of Waldspurger, *La formule de Plancherel pour les groupes p-adiques* (2003),
V.2.2 and V.3.1, printed pp. 293–295.

`compactComparison_inverse_product_norm` uses the left inverse law of the
compact reverse operator and applies the norm identity to a pure tensor.
The common positive factor from the prescribed formal degree cancels,
leaving the product of the probability norms on the two sides.
