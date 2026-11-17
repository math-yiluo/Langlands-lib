# Pinned correction of an aligned affine comparison

This internal construction combines the proved affine inverse-simple-root lift
with the proved all-test correction criterion. Its purpose is to supply the
affine geometric existence step for relative pinned comparisons. It introduces
no new assertion from the literature.

Let `M` and `N` be affine pinned models, and let `A` be a commutative algebra
over both original coefficient rings. Suppose an actual comparison `e` over
`Spec A` comes with a commutative coordinate torus isomorphism `τ`, a commuting
square with the two torus inclusions, and a bijection `σ` between the simple-root
supports such that `τ` carries each source simple-root character to its specified
target character. Suppose also that `e` preserves the canonical positive-coroot
cocharacter.

The theorem `exists_fppf_pinnedCorrection_of_aligned` constructs a scheme `W`,
a map `p : W → Spec A` that is flat, surjective and locally of finite
presentation, and an actual section `z` of the target group pulled back to `W`.
The comparison obtained by pulling back `e` along `p` and then conjugating by
`z` is `IsLocallyPinned`: it preserves the actual torus, the canonical
cocharacter, and the original chosen pinning vectors on every local affine
test. Neither coefficient ring is required to be nonzero or local, and no
affineness or connectedness is required of `W`.

`AlignedAffinePinnedCorrectionStatement` states exactly this implication with
all of the alignment hypotheses explicit. The theorem
`alignedAffinePinnedCorrectionStatement` proves it in every universe.

The implemented proof extracts the unique coefficient unit discrepancies using
`pinningUnitDiscrepancies`. It reindexes those units by `σ.symm` and applies
`exists_fppf_inverse_simpleRoot_values` on the target. The resulting torus
section has inverse character values on every compatible affine coefficient
test. The theorem `preservesLocalPinning_corrected` therefore proves the
pinning-vector clause for the corrected actual comparison.

The supporting construction `normalizedTorusBasePoint` turns a torus point
over `p` into a base section of the canonical split torus over `W`, using the
pullback point equivalence and the canonical split-torus base-change
isomorphism. `normalizedTorusBasePoint_image` proves that its image in the
direct target pullback is exactly the inverse image under
`normalizedBasePointsEquiv` used by the all-test correction theorem. The proof
uses `inclusionOver_pull`, cancels the coordinate and ambient comparison
isomorphisms, and then uses the first-projection equation of the actual
pullback.

Finally, `inclusionOver_comp_torusInner` proves that conjugation by the image
of a normalized torus section fixes the torus inclusion. Naturality of inner
conjugation reduces this to conjugation in the split torus, where the
coordinate point group is commutative. `torusInner_preserves` also proves the
cocharacter clause because the canonical cocharacter factors through that
inclusion. Pulling back and composing these two preservation laws with those
of `e` completes the construction.
