# Connected reductivity of finite separable affine Weil restriction

Author: Worker 110 (proof); placed in this standalone module by Worker 207.

`Langlands.GroupScheme.AffineWeil.isConnectedReductive_restriction` proves
the following. Let `k ⊆ K` be a finite separable field extension (arbitrary
fields, arbitrary characteristic) and let `G` be a connected reductive group
scheme over `Spec K`. Then the actual affine Weil restriction
`AffineWeil.groupScheme k K G` is connected reductive over `Spec k`. The
affineness and smoothness instances that the restriction construction needs
come from `hG` inside the result type.

This module holds the theorem without importing any statement module, so a
consumer such as the parabolic–radical transport proof can use it
independently.

## Proof

The proof extends the base field `k` to its algebraic closure `Ω`. The
published `AffineWeil.embeddingProductIso` identifies this base change of
the actual affine Weil restriction with the categorical product
`GroupScheme.pi` of the actual base changes of `G`, one for each
`k`-embedding `τ : K → Ω`. Every mapped minimal polynomial splits because
`Ω` is algebraically closed. For each embedding the proof installs the
induced `K`-algebra structure on `Ω` and applies the published preservation
of connected reductivity under field extension,
`connectedReductiveFieldExtensionStatement`.

The supporting module `Reductive.FiniteProducts` proves
`isConnectedReductive_pi_of_isAlgClosed`: a finite product of connected
reductive groups over an algebraically closed field is connected reductive.
Transport along the embedding-product isomorphism (`of_iso`) gives connected
reductivity after extension to `Ω`. The published reflection theorem
`IsConnectedReductive.of_fieldExtension` then gives the result over `k`.

This is an internal composition of published Library results and the
accompanying finite-product proof. It adds no perfectness, characteristic or
infinitude restriction and does not use the elementary-subgroup or
Kneser–Tits statements.
