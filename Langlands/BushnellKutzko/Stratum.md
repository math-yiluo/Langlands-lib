# Strata and equivalence

Source: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), `bushnell-kutzko-1993-admissible-dual-gln`, §1.5, definition preceding
(1.5.1) and (1.5.1), printed p. 43 (PDF p. 55).

`Stratum O K V` represents `[𝔄,n,r,b]`. Its fields are a published
`LatticeChain O K V`, the integers `n,r`, an element `b : Module.End K V`,
and the defining conditions `r < n` and `−n ≤ chain.valuation b`.
The hereditary order is `chain.order`; its radical powers and valuation
are precisely the published definitions. A choice of lattice-chain
presentation is part of this representation; equality of two chain
presentations is not asserted.

`Stratum.coset` is the subset `{x | x − b ∈ 𝔓^{−r}}`, so it is
`b + 𝔓^{−r}`. `Stratum.Equivalent` is equality of these cosets, including
when the two chains or integer parameters initially differ. No
order-equality, depth-equality or level-equality result of T5 is assumed
in the definition.

For the original local-field setting take `O = 𝒪[F]`, `K = F`.
The same definition applies in `End_E(V)` by taking
`O = subfieldIntegers F E`, `K = E`, and a lattice chain supplied by the
published subfield-order statement. No local-field instance on `E`
is required to use the definition. The ring, field and vector-space
universes are independent.
