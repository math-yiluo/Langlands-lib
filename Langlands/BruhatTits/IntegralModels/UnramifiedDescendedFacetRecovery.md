# Recovery of descended facets from actual unramified images

This internal unit combines full-facet restriction with global unramified
zero-fixer recovery and exact special-fibre image recovery. It does not introduce
a new translation from the literature.

The downstairs data `B` are valuation building data over a nonarchimedean local
field `F`. The upstairs data `C` are maximal-unramified building data for an
affine group scheme `H` over `UnramifiedClosure F`, and `E` is a supplied actual
unramified zero datum. The group `H` need not be specified as a base change in
these results. The rational-point homomorphism `ρ`, quotient point map `e`, and
affine apartment map `a` satisfy the hypotheses of `facetRestrictionEmbedding`:
downstairs apartment axioms, common downstairs point apartments, equivariance,
apartment compatibility, and exact restriction of every upstairs affine facet
through a point of the apartment image.

`descendedFacet_eq_of_zeroFixer_eq` compares the actual subgroups
`E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc.val)` for full downstairs facets `Fc`.
Each image is nonempty and lies in its full upstairs facet assigned by
`facetRestrictionEmbedding`. The global zero-fixer equality theorem applies to
these two nonempty facet subsets and identifies the full upstairs facets.
Injectivity of the restriction embedding then identifies the full downstairs
facets. It is not necessary to assume that a downstairs facet image is an
entire upstairs facet, or that the two images initially share an apartment.

`descendedFacetZeroFixerEmbedding` is the actual embedding from full downstairs
facets to these subgroups of `H(UnramifiedClosure F)`. Its application theorem is
definitionally the displayed zero-fixer formula. All geometry is at arbitrary
universe `u`.

The model-image result additionally uses a Henselian local domain `R` with
fraction field `UnramifiedClosure F` and algebraically closed residue field.
Two actual relative-component source models map by compatible identity-generic
model homomorphisms into a common target. Their neutral models carry smoothness
and connected fibres as part of their data. Each source's neutral integral-point
subgroup must equal the specified zero fixer for the corresponding downstairs
facet image. Separately, each source subgroup must contain the target neutral
congruence subgroup.

Under these explicit hypotheses,
`descendedFacet_eq_of_unramifiedSpecialFibreImage_eq` identifies the downstairs
facets from equality of the subgroup functors represented by the closed
inclusions of the two actual neutral special-fibre schematic images. Equality
is on every residue-scheme test. The proof uses
`specialFibreImage_eq_iff_integralPoints_eq`, rewrites by the two integral-point
characterizations, and applies the geometric equality theorem above.

This supporting result does not prove the facet-specific congruence
containments, parabolicity, comparison with reductive-quotient images, descent of
image equality from the base residue field, or surjectivity onto all parabolics.
The exact host parabolic order bijection therefore remains a separate obligation.
