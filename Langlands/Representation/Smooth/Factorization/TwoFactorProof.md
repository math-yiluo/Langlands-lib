# Two-factor decomposition of admissible representations

The theorem `Langlands.flathTwoFactor` proves exactly the published proposition
`Langlands.FlathTwoFactorStatement`. Its seven independent universe parameters,
in order, are `uG₁`, `uG₂`, `uV₁`, `uV₂`, `uW₁`, `uW₂`, `uV`.
The theorem adds no hypothesis. The target's Lean/Markdown pair and its imports
are unchanged.

The proof forms the conjunction of four imported theorems in the order of the
target:

| Clause | Theorem | Implemented argument |
| --- | --- | --- |
| Fixed vectors | `Langlands.productFixedVectors` | Linear retractions prove injectivity of the tensor of fixed-subspace inclusions. Basis coefficients show its range is exactly the product-subgroup fixed space. |
| External tensors | `Langlands.admissibleExternalTensor` | Tensor induction gives smoothness. The fixed-vector formula gives admissibility for every open subgroup. Schur's lemma and Jacobson density extract a nonzero pure tensor from a nonzero subrepresentation; irreducibility of both factors then makes that subrepresentation the whole tensor product. |
| Existence | `Langlands.admissibleProductFactorization` | A minimal fixed-space dimension argument with compact averaging constructs the first irreducible factor. The second is its intertwiner multiplicity space. Schur's lemma and Jacobson density make evaluation an equivalence; both factors are proved admissible and irreducible. |
| Uniqueness | `Langlands.admissibleProductFactorUniqueness` | Restrict an external-tensor equivalence to each group and cancel the other factor's trivial multiplicity space, commuting tensor factors for the second restriction. |

The detailed proofs and their dependencies are described in
[TwoFactorFixedVectorsProof](TwoFactorFixedVectorsProof.md),
[TwoFactorExternalTensorProof](TwoFactorExternalTensorProof.md),
[TwoFactorExistenceProof](TwoFactorExistenceProof.md), and
[TwoFactorUniquenessProof](TwoFactorUniquenessProof.md).
This module introduces no additional representation-theoretic argument.

The source assertion is D. Flath, *Decomposition of representations into tensor
products* (1979), Theorem 1, printed pp.179–180 / one-based PDF pp.175–176
(registered `flath-1979-tensor-products`), and David Renard,
*Représentations des groupes réductifs p-adiques*, 2026 version, III.1.14,
printed pp.66–67 / one-based PDF pp.72–73
(registered `renard-2026-representations-groupes-reductifs-padiques`).
The arbitrary-subgroup fixed-vector clause is the algebraic strengthening
already specified by the published target. The existence proof uses the direct
multiplicity-space construction described above, rather than Flath's
Hecke-algebra and inductive-limit route.
