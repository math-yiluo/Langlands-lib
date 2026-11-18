# Keeping a compatible split component inside the standard Levi

This internal algebraic transport keeps the same actual split torus and its
same map into the fixed maximal split torus when passing from the ambient
group to an outer standard Levi. It follows from published represented
subgroup, standard-family and closed-embedding results, and introduces no
new original-literature assertion.

For nested selected root sets `R` contained in `J`,
`standardLeviComponentRestrictionHom` takes any original representative
`m : M -> G` of the inner standard Levi of `R` and factors it through the
canonical outer Levi `Standard.leviScheme i nu J`. Containment follows from
the published `standardLevi_mono_of_exists`, with standard-cocharacter
existence supplied by the published theorem. The definition uses the exact
represented-subgroup `factorHom` and its `_comp` theorem states that
composition with the canonical outer Levi embedding recovers `m`.

`IsCompatibleStandardSplitComponent.leviScheme` assumes connected reductivity,
a maximal split torus, a generic cocharacter, `J` contained in the ambient
simple roots, `R` contained in `J`, and the original
`IsCompatibleStandardSplitComponent i nu R A q`. It concludes compatibility
inside the intrinsic outer Levi for precisely the same `A` and `q`.

The proof retains the original representative group `M`, its connected
reductivity, and the original split component `a : A -> M`. Only the map
`M -> G` is read through the proved outer-Levi factor. The published
standard-family intersection comparison identifies the inner standard Levi
in the outer one with the exact preimage of the original inner subgroup.
The published represented-subgroup comap theorem proves that the restricted
map represents this preimage. Closedness follows by cancellation against
the closed outer embedding. Finally, cancellation of that monic embedding
proves the exact component equation `a` followed by the restricted map equals
`q` followed by `Standard.leviTorusHom i nu J`.

The implementation explicitly checks that the canonical `leviTorusHom`
equals the factor appearing in the published standard-family comparison:
both compose with the same monic Levi embedding to the original `i`. It
uses this equality before applying the intersection comparison.

All statements are over arbitrary fields, with no local-field topology,
valuation, characteristic, splitness or quasisplitness restriction. The
root subsets need not be separately presented as finite sets. The original
component is not replaced by an unrelated choice.

No equality between the ambient and intrinsic component chambers is claimed.
Their outside-root sets differ. Contraction and cofinality on the larger
intrinsic chambers, compact-open neighborhood bases and full simultaneous
standard-basis inheritance remain separate obligations. This module contains
no analytic coefficient or wave-packet estimate.
