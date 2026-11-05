# Pseudo-parabolic descent under split-radical quotients

`Langlands.GroupScheme.pseudoParabolicSplitRadicalQuotient.{u}` proves the
unchanged published proposition
`Langlands.GroupScheme.PseudoParabolicSplitRadicalQuotientStatement.{u}`.
The field, universe, actual groups, supplied fppf quotient and pseudo-parabolic
predicate are exactly those of that statement. In particular the proof applies
to finite and imperfect fields in every characteristic.

The source of the original pseudo-parabolic inclusion is smooth, connected and
affine by `PseudoParabolicStructureProof`. The proof applies
`HomImage.exists_image` to its composite with the supplied quotient. This
produces an actual closed subgroup `j` of the target and a commuting fppf
projection from the original subgroup onto `j`.

The supplied split radical is smooth, connected and unipotent. Transport from
this kernel representative gives `HasSmoothConnectedUnipotentKernel` for the
original quotient. Its `smooth` theorem proves that the original quotient is
smooth. The pseudo-parabolic presentation supplies a ground-field radical of
the source, and `unipotentRadicalExistence` supplies one in the target.
`radical_isFppfImage` proves that the latter is the actual fppf image of the
former. `Dynamic.parabolic_isFppfImage` gives the same conclusion for the
dynamic parabolic of the original cocharacter and its composite with the
quotient.

`IsFppfProduct.of_fppfImages` transports the original product presentation to
`j`, using these two factor images and the fppf image constructed by
`HomImage.exists_image`. This is precisely the unchanged
`IsPseudoParabolicSubgroup j` predicate.

Finally the split radical lies in the supplied ground-field radical by
greatestness, and the latter lies in the original pseudo-parabolic product.
The quotient's exact kernel equality therefore shows that the original
subgroup contains the full actual kernel. Applying
`IsFppfImage.comap_eq_of_kernel_le` gives the required exact inverse-image
equality of subgroup functors on every relative scheme. No pointwise
surjectivity on the original test scheme or existing local sections are
assumed.

This is a derived assembly of the imported constructions and proofs. Its
literature target is the split-radical descent in CGP Lemma C.2.1, as documented
in the published statement's companion Markdown. The implemented route uses
the image of the ordinary ground-field radical directly and does not require
the separate equality of products with ordinary and split radicals.
