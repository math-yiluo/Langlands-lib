# Actual simply connected Weil presentations and conditional pair descent

Worker 634, with Worker 632's finite-family assembly and tensor-base recovery.

AffineSimplyConnectedWeilPresentation supplies the actual finite projective
étale algebra, surjective finite base, reductive factor group with simply
connected almost-simple geometric fibres, and the actual Weil-restriction
isomorphism required by the target's existence clause. Forgetting these data
gives precisely its existential form.

A supplied finite product of reductive groups with these fibre properties
produces a presentation over the finite product algebra. The imported actual
disjoint-family construction identifies its Weil restriction with the given
product and transfers both geometric fibre properties. Nontrivial geometric
fibres force a nonempty factor index wherever the base has a point, so the
finite base map is surjective even when the original base is empty.

Assuming the unchanged AffineWeilPairEtaleDescentStatement, presentations on any
covering family of étale affine charts descend. That supplied statement gives
the actual tensor-algebra and group recoveries on every chart. Their spectra
cover the descended finite base; simple connectedness reflects at a point of
any base change by the actual field/geometric-fibre comparisons. The descended
factor therefore has simply connected fibres as well as the almost-simple
fibres already supplied by the descent statement. This helper does not assert
that pair descent itself holds.

These are internal constructions from the imported finite-family, geometric
comparison and actual tensor-base recovery results, following the local
product/descent route of Conrad, *Reductive group schemes* (2014),
Proposition 6.4.4, pp.232–233.

The proof of surjectivity uses `AffineAdjointWeilPresentation.surjective_productBase` on the same nontrivial geometric fibres.
