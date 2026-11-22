# Coherence of pullback for products of p-divisible groups

`baseChangeProdIso_id` says that the product comparison along the
identity coefficient map followed by the identity comparisons on the
two factors gives the identity comparison on the original product.

For commutative rings in an algebra tower `R → S → T`,
`baseChangeProdCompIso` compares the direct pullback of a product of two
actual p-divisible groups with the product of their successive pullbacks.
It applies the composition comparison to the product and then applies
the product comparison at each step. By `baseChangeProdIso_comp`, its
forward map agrees with applying the direct product comparison followed
by the composition comparison on both factors. Both proofs test on the
actual product projections and use naturality of the identity or
composition comparison on each projection.

These coherence identities are derived from the product projections.
They apply to the coefficient changes of the two tower factors in the
split presentation of Rapoport–Zink (1996), §6.43, printed p. 309
(PDF p. 321), before (6.17).
