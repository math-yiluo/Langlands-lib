# The commutative algebra for the cyclic lift

This internal helper for the proof of Bushnell–Kutzko (1993), (2.4.1)(iii), is motivated by the lifting of the residual polynomial and the cyclic action in §2.5 (especially (2.5.7)–(2.5.11)). It packages the two polynomial relations separately from any filtration or field claim.

Given a monic polynomial `Q` of positive degree with unit constant coefficient, the first `AdjoinRoot` algebra contains a unit root `U`: the relation obtained by writing `Q = X * Q.divX + C (Q.coeff 0)` makes the product of the root and the evaluation of `Q.divX` a unit. Over that algebra, adjoin a root `T` of `X ^ h - C (π * U ^ a)` for `h > 0`, a base-field unit `π`, and an integer `a`. This root is a unit because its `h`th power is a unit. The two monic power bases compose by scalar towers; swapping the indices gives the rectangular basis with vectors `T ^ m * U ^ l`. No irreducibility or field structure on either root algebra is asserted here.
