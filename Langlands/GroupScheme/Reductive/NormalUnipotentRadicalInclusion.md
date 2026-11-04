# The radical of a normal subgroup inside the ambient radical

Worker 1372. Internal consequence of normalized conjugation, full radical
stability under smooth actions, greatest radical containment and represented
subgroup factorization.

Let `k : Type u` be algebraically closed, let `G` be smooth, and let `H` be
smooth, connected and affine. Suppose `i : H ⟶ G` is a closed inclusion
whose full range functor is normal. For a supplied unipotent radical
`s : V ⟶ H`, `IsUnipotentRadical.normalAmbientAction` constructs an actual
action of `G` on `V` by group automorphisms.

The construction applies the existing normalized-conjugation action of
`G` on `H` to the published radical-action construction. Smoothness of `G`
and the stated hypotheses on `H` discharge all hypotheses of that
construction. `normalAmbientAction_act_comp` identifies its action after
the composite inclusion `s ≫ i` with ambient conjugation by every point
on every test scheme. The general-base helper
`ofNormalizedConjugation_act_comp` records the corresponding point formula
for the existing normalized-conjugation action.

Consequently `IsUnipotentRadical.isNormal_comp` proves that `s ≫ i` has
normal full range in `G`. Given any supplied ambient radical `r : U ⟶ G`,
the composite is a smooth connected unipotent normal closed subgroup, so
the greatest property of `r` gives `range_comp_le`. Rewriting that
containment at each point gives `le_comap`: the radical of `H` lies in the
inverse image of the radical of `G`.

`IsUnipotentRadical.normalSubgroupFactor` constructs the resulting actual
homomorphism `V ⟶ U`. It uses the existing factorization through the
subgroup represented by `r`. Its composite with `r` is `s ≫ i`, it is
unique with that composite, and it is a closed subgroup inclusion because
both `r` and the composite are closed.

No smoothness, affineness or connectedness premise on a test scheme is
imposed. Affineness and connectedness of `G` are not required for these
conclusions; the supplied radical provides the needed greatest property.
The module proves one containment in the radical-intersection target.
The reverse containment, including its possible nonreduced tests, remains
unproved here. This contribution does not complete
`NormalUnipotentRadicalIntersectionStatement` or the host semigroup
comparison target.
