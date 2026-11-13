# Generic ampleness from the closed ample-fibre locus

Worker 833's conditional reduction assumes both
`AbelianFibreAmpleLocusClosedStatement` and
`ProperAffineFibrewiseAmpleStatement`. It targets
`NoetherianAffineAbelianGenericAmpleStatement` and supplies neither assumed
geometric input.

The first lemma factors a field-valued point of any base scheme through
the spectrum of its image point's residue field. Pasting the two actual
pullback squares identifies its base change with a field extension of
the residue-field fibre. Affine pullback preserves the given ampleness
along this scheme isomorphism, and the published
`fieldBaseChangeAmpleReflection` theorem reflects it to the specified
residue-field fibre bundle.

For the canonical fraction-field point of a domain, the image prime is
the zero ideal because the algebra map is injective. Its closure is
therefore the whole spectrum. The closed ample-fibre locus contains this
point by the first lemma, so it contains every base point. The supplied
fibrewise-to-total criterion then proves ampleness of the same total
bundle over the noetherian affine base.

This is an internal reduction using the Library's actual scheme and
sheaf pullbacks, not a construction of a dual scheme or a proof of
closedness. The target statements are published in the Library. The
conditional theorem does not give an unconditional exact proof until
both assumed geometric inputs have been proved.
