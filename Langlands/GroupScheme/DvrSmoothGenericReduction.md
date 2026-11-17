# Smooth-generic reduction from potential geometric reducedness

Workers 572 and 336.

`DvrSmoothGenericReduction.reduction R K G hPotential` constructs actual
witnesses for the preliminary group reduction, assuming the explicit
general scheme premise
`Langlands.AlgebraicGeometry.DvrPotentialGenericReductionStatement.{u}`.
The resulting `Reduction G` contains a same-universe DVR extension,
a flat surjective base morphism, an actual flat separated finite-type
group `P`, and an actual finite surjective group homomorphism to the
base change of `G`. The actual generic fibre of `P` over the new
fraction ring is smooth and affine.

The theorem
`DvrSmoothGenericReduction.dvrSmoothGenericReduction_of_potential`
packages this construction as the unchanged
`DvrSmoothGenericReductionStatement.{u}`. Both the construction and
its theorem retain the general scheme premise; this module does not
prove that premise or the original finite smooth total-cover theorem.

## Implemented construction

Apply the general scheme premise to the actual scheme underlying `G`
over the original DVR. It supplies a DVR `R'` and a flat surjective
morphism on spectra. Its geometric-reducedness conclusion is exactly
the hypothesis needed to form the smooth reduced generic subgroup of
the actual base change `G'`.

The actual generic fibre of `G'` is affine, by
`DvrCoverAssembly.affine_generic`. That lemma extends the injective
ring map underlying the faithfully flat base map to the chosen
fraction fields, and then uses two successive pullbacks and their
canonical comparison isomorphism. This also handles an arbitrary
original fraction field `K`, whereas the conclusion uses the
canonical `FractionRing R'`.

`DvrGenericReduction.group G'` closes the actual smooth reduced generic
subgroup inside `G'`. Its implemented properties give flatness, finite
type, separatedness, smooth and affine generic fibre, and a finite
surjective actual group homomorphism. Surjectivity uses the dense
ambient generic fibre and the closed image of the closure inclusion.
Selecting the resulting nonempty witness gives `reduction`; unpacking
its fields gives the proposition theorem. All rings and schemes stay
in the arbitrary original universe `u`.

## Scope and provenance

This implements the preliminary step in the proof of Brian Conrad's
Corollary A.4, author-preprint p.29 of Prasad and Yu, *On quasi-reductive
group schemes*. The literature uses the reduced total group. The
implemented argument instead closes the reduced generic subgroup,
using the Library's actual schematic-closure construction. The
potential-geometric-reducedness input is isolated as a general scheme
statement, derived from the preliminary clause of A.2/A.5 and the
henselian DVR reduction. Stable normalization and total smoothness
are separate later steps of A.4.

Worker 572 implemented the group-specific reduction, including the
arbitrary-field reduced subgroup and the surjectivity argument for
its closure. Worker 336 supplied the generic-affineness base-change
lemma used from `DvrCoverAssembly`. The candidate includes exact
supporting Lean/Markdown pairs so that its imports can be integrated
together; imported normalization interfaces are statements, not
asserted proofs of the geometric prerequisites.

Registered source:
`prasad-yu-2006-quasi-reductive-author-preprint`, SHA-256
`138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`.
