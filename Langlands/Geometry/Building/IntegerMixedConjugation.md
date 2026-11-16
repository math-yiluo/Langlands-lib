# Integer-valued mixed doubled-opposite conjugation

This internal helper adapts the two coordinate estimates of
`MoyPrasadMixedConjugation` to `IntegerValuationBuildingData`. It uses the
rank-one and doubled-root estimates of `IntegerRootConjugation`, with an
explicit order-one unit hypothesis and no apartment-axiom assumption.

`mul_double_opposite_mem_block_centralizer_root` applies mixed real-depth
exchange to the inverse product. This retains the doubled input depth in
the negative root block. `conjugate_double_opposite_mem_root_centralizer_block`
uses the opposite reflection factor pair of the depth-zero ordinary element.
Translation conjugation places the doubled-root input at depth `r + 4t`.
Mixed exchange against the opposite factor at depth `-t` leaves the positive
coordinate in the original depth-`r` block. The doubled-root subgroup commutes
with the other opposite factor, giving the asserted conjugation formula.

Both are coordinate estimates in the actual rational-point group. Neither
asserts any depth for the centralizer coordinate. Their provenance is the
cited Library proofs, adapted using the proved integer-valued root geometry.
