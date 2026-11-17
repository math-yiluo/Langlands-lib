# Adjoint Weil existence reduced to local products and pair descent

Worker 632; shared descent statement by Worker 5254.

This internal construction gives the global existence assembly for the
affine adjoint Weil-restriction problem, conditional on local adjoint
pinned presentations and the generic almost-simple pair descent
statement. It is motivated by Brian Conrad, *Reductive group schemes*
(2014), the proof of Proposition 6.4.4 and Remark 6.4.5, pp.232–233,
registered as `conrad-2014-reductive-group-schemes`.

`AffineAdjointWeilPresentation.precompose` transports a supplied actual
Weil presentation along an isomorphism of the original group.

`ofEtaleLocal` assumes the proposition
`AffineWeilPairEtaleDescentStatement` and a covering family of étale
algebras, each carrying an actual adjoint almost-simple presentation of
the original base-changed group. It applies that generic statement after
forgetting adjointness, then uses its original local pair comparisons
and the proved recovery-covering theorem to establish adjointness of
every geometric fibre of the descended group. The result retains the
actual algebra, its finite/projective/étale properties and surjectivity,
the reductive group, both fibre conditions and the original group
isomorphism.

`ofPinnedCharts` constructs the required covering family from the
proved adjoint pinned atlas. It retains each chart's original algebra
structure and verifies its étaleness and coverage. A supplied
presentation of each adjoint pinned model is precomposed by its actual
chart comparison and then passed to `ofEtaleLocal`.

The construction works over every commutative ring in the arbitrary
universe `u`, including the zero ring and its empty spectrum. It adds
no extra hypotheses on the group or base to those of the target.
It is explicitly conditional: it does not prove pair descent or
construct the local component product, and it does not prove the
uniqueness part of the final target. `AdjointWeilPresentation.ofProduct`
supplies its local presentation input once the component-product
existence theorem is available.
