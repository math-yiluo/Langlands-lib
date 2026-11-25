# The augmentation quotient I/I² of the integral group ring

Module `Nyll.GaloisCohomology.GroupTheory.Augmentation`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For any group G, let I be the augmentation ideal of the integral group ring ℤ[G]. The file proves the classical isomorphism `Gᵃᵇ ≅ I/I²`, `g ↦ (g − 1) mod I²`. It is set up for the comparison of transfer and augmentation, and for reuse in a proof of Witt's transfer theorem.

## Main definitions and results

All are in the namespace `GroupTheory.Augmentation`.

- `IntegralGroupRing G` is `MonoidAlgebra ℤ G`; `augmentation G : ℤ[G] →+* ℤ` sends each group element to 1, so it is the sum of the coefficients (`augmentation_apply`).
- `ideal G` is its kernel, a two-sided ideal. `square G` is the two-sided ideal spanned by products of two elements of `ideal G`, contained in it (`square_le_ideal`). `squareInIdeal G` is `square G` as an additive subgroup of `ideal G`, and `Quotient G` is `ideal G ⧸ squareInIdeal G`.
- `deltaElement G g` is `g − 1` in the ideal. `deltaCombination_eq_of_mem_ideal`: an element of augmentation zero equals `∑ a_g (g − 1)` over its support.
- `deltaClass G g` is the class of `g − 1`; it sends 1 to 0 and products to sums (`deltaClass_mul`). `deltaMonoidHom` and its factorization through the abelianization, `deltaAbelianization`, are the resulting homomorphisms.
- `deltaAbelianization_surjective` and `deltaAbelianization_injective`, packaged as `deltaAbelianizationEquiv : Abelianization G ≃* Multiplicative (Quotient G)`.
- `deltaClass_eq_zero_of_mem_commutator`: elements of the commutator subgroup have class zero.

## Proof

Additivity comes from the identity `gh − 1 − (g − 1) − (h − 1) = (g − 1)(h − 1)`. Surjectivity uses the expansion of an augmentation-zero element in the elements `g − 1`, with preimage the product of the classes `Abelianization.of g` raised to the coefficients `a_g` (`deltaPreimage`). For injectivity, `linearization G : ℤ[G] →+ Additive Gᵃᵇ`, `∑ a_g g ↦ ∑ a_g [g]`, kills products of two elements of I and therefore all of I² (by induction over the span, `linearization_eq_zero_of_mem_square`). It descends to `quotientLinearization` on `Quotient G`, which is a left inverse of `deltaAbelianization`.

## Watch for

- `Quotient G` is an additive group; the isomorphism is stated with `Multiplicative (Quotient G)` as target.
- I² is defined as the two-sided ideal spanned by products, and the quotient is taken only as abelian groups, not as ℤ[G]-modules.
- No finiteness of G is assumed.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/GroupTheory/Augmentation.lean`: the Lean file is the source byte for byte (SHA-256 `1fc45ba0533c290a3829eb7b7bbc9600ce67fd5ff5388e9f792768b9678c3f7e`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
