# Induced filtrations on a subgroup and on a quotient

Module `Nyll.ValuedFieldTheory.Ramification.Herbrand.Quotient`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file supplies the finite-group bookkeeping behind Herbrand's theorem on quotients and its tower form. Given a decreasing filtration `(G_n)` of `G` by normal subgroups and a subgroup `H`, it builds the filtration induced on `H` and, for normal `H`, the image filtration on `G/H`; it proves that the orders multiply at every level, and that filtrations and Herbrand functions can be moved along group isomorphisms. No field or valuation occurs.

## Main definitions and results

- `subgroupFiltration F H`: the filtration `G_n ∩ H` of `H`.
- `quotientImageFiltration F H`: for normal `H`, the filtration of `G/H` by the images `G_n H / H`.
- `lowerToQuotientImageHom` maps `G_n` onto the `n`th image group (`lowerToQuotientImageHom_surjective`); `lowerToQuotientImageKerEquiv` identifies its kernel with `G_n ∩ H`.
- `card_subgroupFiltration_mul_card_quotientImageFiltration`: for finite `G`, `|G_n ∩ H| · |G_n H / H| = |G_n|` at every level.
- `transportEquiv F e`: the filtration carried along a group isomorphism `e : G ≃* G'`, with `lowerEquivTransportEquiv` and `card_lower_transportEquiv` (orders are preserved) and `transportEquiv_lower_eq_map` (the transported level is the image `e(G_n)`).
- `herbrandFunction_transportEquiv`, `inverseHerbrandFunction_transportEquiv`: for finite groups, `φ` and `ψ` do not change under transport.
- `quotientImageTransport F H e`: the image filtration carried to any group `G'` isomorphic to `G/H`. For it the file gives the cardinality factorization (`card_subgroupFiltration_mul_card_quotientImageTransport`), the invariance of `φ` and `ψ`, and `quotientImageTransport_lower_eq_iff`, which rewrites an equality of a transported level with a subgroup `B ⊆ G'` as `image of G_n in G/H = e⁻¹(B)`.
- `subgroup_map_equiv_eq_iff_eq_comap`: for an isomorphism `e`, `e(A) = B` if and only if `A = e⁻¹(B)`.

## Proofs

The factorization is Lagrange's theorem for the surjection `G_n → G_n H/H` with kernel `G_n ∩ H`. Invariance of `φ` uses the lemma that `φ` depends only on the orders of the `G_n`; invariance of `ψ` follows from injectivity of `φ`.

## Watch for

The image filtration is only the image of the given filtration. As its docstring stresses, the file does not claim that it is the lower ramification filtration of a quotient extension; that identification is what Herbrand's theorem provides, and it is not proved here.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/Herbrand/Quotient.lean`: the Lean file is the source byte for byte (SHA-256 `53d83c7fe22abae2aca5ef8d2eb4271b1f2297f6b6c65d71f1911414a9382b85`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
