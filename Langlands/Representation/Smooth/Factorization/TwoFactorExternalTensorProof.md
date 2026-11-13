# Admissibility and irreducibility of external tensor products

The theorem `Langlands.admissibleExternalTensor` proves exactly
`Langlands.AdmissibleExternalTensorStatement`, the tensor
preservation clause of Flath's Theorem 1, printed pp.179–180
(`flath-1979-tensor-products`), and Renard III.1.14, printed pp.66–67
(`renard-2026-representations-groupes-reductifs-padiques`).

Smoothness follows by tensor induction: the product of two open stabilizers
fixes a pure tensor, and the smooth vectors are closed under addition.
For any open subgroup of the product, its inverse images along the two
coordinate inclusions are open subgroups whose product it contains.
The fixed-vector tensor identification bounds its fixed space by a tensor
of two finite-dimensional fixed spaces, proving admissibility with the
all-open-subgroups convention.

For irreducibility, admissible Schur makes the first factor's endomorphisms
scalar. The published Jacobson density lemma then makes an arbitrary
first-factor linear endomorphism agree with a group-algebra element on the
finitely many first coefficients of a given tensor. Consequently every
product subrepresentation is stable under these linear endomorphisms.
A rank-one basis-coordinate map extracts a nonzero pure tensor from any
nonzero subrepresentation. The subrepresentations obtained by fixing one
tensor factor then show, using irreducibility of the two factors, that it
contains every pure tensor. Tensor induction makes it the whole space.
Nontriviality follows from the tensor of two nonzero vectors over a field.

The slice subrepresentations, coefficient extraction and stability lemmas
are internal algebraic steps derived for this proof. The proof retains
independent group and representation-space universes.

The `TwoFactorExternalTensor.external` abbreviation reuses the published
`MixedProductTensor.external` definition. The pullback-and-tensor action and
its independently quantified factor universes are unchanged.
