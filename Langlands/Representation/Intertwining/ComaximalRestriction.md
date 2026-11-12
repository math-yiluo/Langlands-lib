# Restriction of intertwiners under comaximal central kernels

Author: Worker 135. This is an internal algebraic construction for the proof of
Renard VII.4.1. It does not establish opposite regularity for Langlands triplets.

Let `rho` and `tau` be complex representations of a group `H`, and let `S` be a
subrepresentation of `rho`. Let `a : B -> H` be a monoid homomorphism with central
image. If the kernels of the `C[B]` actions on `tau` and `rho/S` sum to the whole
algebra, restriction gives a linear equivalence from `Hom_H(rho,tau)` to
`Hom_H(S,tau)`. All carrier universes are independent and no representation is
assumed finite-dimensional.

The proof writes `1=x+y`, where `x` kills `tau` and `y` kills `rho/S`. The action
of `y` sends `rho` into `S` and is `H`-equivariant by centrality. Every map from
`S` to `tau` extends by composing with this action. Naturality of algebra actions
and the identity action of `y` on `tau` prove both uniqueness and the restriction
identity. `restrictionEquivOfComaximal` packages the bijective restriction map as
a linear equivalence.

If `S` is equivariantly isomorphic to an admissible irreducible `tau`,
`endomorphismEquiv` identifies `Hom_H(S,tau)` with `End_H(tau)`. The published
`admissibleSchur_homEquiv` identifies the latter with the scalar field, so
`finrank_intertwining_eq_one_of_comaximal` proves the dimension is one. Only this
last corollary uses a topology on `H`; no local compactness or nonarchimedean
hypothesis is required for the algebraic construction.

The provenance is internal: this is the elementary comaximal-kernel argument
underlying the regularity applications, expressed using the published
`groupAlgebraKernel` and Mathlib representations. It asserts no geometric or
spectral input. In the eventual application, `rho` is `r_Pbar i_P(tau)` and `S`
is its identity-cell support image. Separate geometric arguments must identify
`S` with `tau` and prove the required comaximality.
