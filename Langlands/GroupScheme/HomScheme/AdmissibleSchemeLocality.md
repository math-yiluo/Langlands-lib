# Absolute membership and torus locality for actual subgroups

Author: Worker 1726.

This internal module supplies the adapters for applying scheme gluing to actual
subgroup functors. It derives all assertions from the existing all-test subgroup
membership, base-change point equivalence, represented-subgroup isomorphism,
and locality of the relative torus property.

`SubgroupFunctor.schemeCondition` takes a map from an arbitrary scheme to the
ambient scheme and tests membership using its induced structural map to the
base. `schemeCondition_iff_mem` identifies this with membership on every original
relative test. Identity maps between the two equal-base presentations transfer
membership in both directions. Arbitrary restriction follows from subgroup
functoriality. If the subgroup has Zariski-local membership, its absolute
condition is detected on any open cover of the source, by applying the original
locality theorem to the canonical relative point.

`schemeCondition_baseChange_iff` identifies this absolute condition after
composition with the original ambient pullback projection with the condition
for the base-changed subgroup. It uses exactly the base-change point adjunction.
`schemeCondition_iff_exists_of_isRepresentedBy` identifies a represented
subgroup's condition with factorization through the same actual underlying
scheme morphism. A scheme factorization automatically respects the induced
structural maps to the base, so it gives the required relative point.

Finally, `isAdmissible_of_isClosedRepresentable_of_openCover` starts with an
actual closed representative of a subgroup which is admissible after base
change along each member of a Zariski base cover. On each member the base change
of the global representative and a chosen local torus representative represent
the same subgroup. Their represented-subgroup Yoneda isomorphism makes that
base change a torus. Torus locality on the base gives a global relative torus,
so the original subgroup is admissible.

The result is uniform in the arbitrary universe `u`; all scheme tests may be
nonaffine and nonreduced. The last theorem assumes closed representability and
does not itself construct a closed immersion by descent. That construction and
unconditional effective admissible descent remain separate obligations.
