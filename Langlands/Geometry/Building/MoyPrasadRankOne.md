# Rank-one depth exchange with the actual centralizer filtration

This internal construction refines the published actual opposite-root factorization using the supplied centralizer filtration's commutator friendliness.

For elements `u ∈ U_{a,x,r}` and `v ∈ U_{-a,x,s}` with `r,s ≥ 0` and `r+s > 0`, it constructs `v' ∈ U_{-a,x,s}`, an actual centralizer point `z ∈ Z(F)_{r+s}`, and `u' ∈ U_{a,x,r}` with `u v = v' j(z) u'`. The root depths are unchanged. Identity factors are handled directly.

For the other case, the actual root valuations of `u` and `v` are finite real numbers `t ≥ r` and `t' ≥ s`. Published rank-one factorization gives `v'`, the centralizer factor and `u'` with valuation bounds `t'` and `t`. The actual representing centralizer isomorphism lifts the central factor to `Z(F)`. Rewriting the product equality gives
`v⁻¹ u v u⁻¹ = (v⁻¹ v') j(z) (u' u⁻¹)`.
The outer factors belong to the required opposite root groups. Commutator friendliness therefore puts `z` in the original centralizer filtration at `t+t'`, and antitonicity puts it at `r+s`.

`rankOneMoyPrasadCoordinates` packages these actual coordinates with their multiplication identity, and the final theorem records the literal set-product inclusion. The actual opposite factor pairs and root-span prerequisites are discharged by published connected-reductive results. No apartment-axiom premise or whole product-covering premise is used. This is exchange for the two ordinary opposite root-depth subgroups; it does not assert exchange of the entire two-factor indivisible-root blocks when the root system is nonreduced, the full Moy–Prasad covering theorem, covariance or the host simultaneous-basis statement.
