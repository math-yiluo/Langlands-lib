# The affine open decomposition of the moduli of subtori of `GL_n`

`TorusSubgroupModuli.generalLinearAffineSum` proves `GeneralLinearAffineSumStatement`.
Over `Spec R`, the statement takes a parameter scheme with a supplied universal
closed relative-torus inclusion into the pullback of `GL_n`, for a finite
matrix index `n` with decidable equality.

The Lean proof introduces these data and the three hypotheses `IsClosedSubgroup j`,
`RelativeTorus.IsTorus K` and `IsUniversal j`, and applies
`OrderedProjectorScheme.exists_disjoint_affineOpen_cover` from
`Langlands.GroupScheme.Torus.OrderedProjectorAffineSum`. That theorem's conclusion
is exactly the conclusion of the statement: an index type in `Type u` and a family
of affine, pairwise disjoint opens of `M.left` whose supremum is `⊤`.

That theorem is proved as follows. The ordered-projector scheme is affine over
`Spec R`. A finite family of distinct characters generating the
lattice of a split torus gives a chart map by the representing property of the
universal family. An étale splitting neighborhood at each moduli point yields
projectors on an affine open with fixed weight support. These projectors
classify the restriction of the universal torus and give a local factorization
through a chart.

The overlap of two charts is a finite disjoint union of copies of the second
chart indexed by matchings of the weights. Pullback along the étale chart
neighborhoods proves that the chart map is finite étale by descent. The
resulting finite surjection from the affine source to its open image gives
affineness of the image. When two images meet, the overlap supplies a weight
matching and relabelling identifies the images. Indexing by distinct chart
images gives the required pairwise disjoint affine open cover of the parameter
scheme.
