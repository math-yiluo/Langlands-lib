# The actual quadratic star field lies in the special-linear cocycle cover

Author: Worker 239.

This internal unit relates the actual Tits star action to a supplied all-test
special-linear Galois presentation. `HasOuterDiscrepancy` is the outer version
of the earlier inner predicate: the discrepancy first applies inverse
transpose and then conjugates by the coefficient image `X` of the supplied
representative, so its formula is `g ↦ X (g⁻¹)ᵀ X⁻¹`.
`HasStarDiscrepancy` records that a supplied family of representatives gives
the inner formula for every absolute Galois lift with trivial star action,
and the outer formula for every lift with nontrivial star action. These are
hypotheses, not existence conclusions.

Inverse transpose commutes with coefficient maps. Evaluating an outer formula
for the identity discrepancy on the spectrum of the cover field, and using
the canonical global-sections equivalence, would make inverse transpose inner
on `SL(L)`. The elementary three-index obstruction excludes this when `n ≥ 2`.
It follows that every absolute Galois element fixing the embedded cover field
has trivial star action.

The Galois fixed-field correspondence now shows that the actual `d.starField`
is contained in the image of that cover field. `starFieldToCover` constructs
the resulting `K`-embedding into the cover, and
`embedding_starFieldToCover` identifies its composite into the separable
closure with the actual inclusion of `d.starField`. For any supplied lift,
`star_trivial_iff_fixes_starField_cover` identifies trivial star action with
pointwise fixation of this embedded subfield.

Finally `StarImagePair.two_le` observes that a nontrivial reversal on `Fin n`
requires `n ≥ 2`. Combined with the already published quadratic-star-field
results, the containment applies to the field required in the outer type A
presentation. The proofs use no classification or downstream rank-one result,
and impose no characteristic restriction. They construct neither a Hermitian
matrix nor the final descended presentation.
