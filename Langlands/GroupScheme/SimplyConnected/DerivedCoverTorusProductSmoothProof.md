# Smoothness of derived-cover and maximal-torus multiplication

Authors: Worker 133 and Worker 1554.

`Langlands.GroupScheme.derivedCoverTorusProductSmooth` proves the existing
`Langlands.GroupScheme.DerivedCoverTorusProductSmoothStatement.{u}`.
For every field `k : Type u` and the supplied group schemes and maps
`d : D → H`, `π : C → D`, and `i : T → H`, the hypotheses are exactly
`IsSimplyConnectedDerivedCover d π` and `IsMaximalTorus i`. The conclusion is
scheme smoothness of the actual ordered multiplication map
`subgroupProductMap (π ≫ d) i : C ×_k T → H`. The universe and characteristic
are unrestricted.

The implemented proof applies
[`derivedCoverTorusProductSmooth_of_preimage_of_surjectivity`](DerivedCoverTorusProductSmoothReduction.md)
to the two proved structural statements:

- [`derivedCoverMaximalTorusPreimage`](DerivedCoverMaximalTorusPreimageProof.md)
  makes the full scheme-theoretic pullback `C ×_H T` a torus.
- [`derivedMaximalTorusProductSurjectivity`](../Derived/MaximalTorusProductSurjectivityProof.md)
  gives scheme surjectivity of `D ×_k T → H`.

The reduction derives smooth affine structure morphisms for `H`, `C`, and
`T` from the two target hypotheses. The first structural theorem supplies
smoothness of the full intersection. The central isogeny `π` is surjective,
so base change on the first factor and composition transfer the second
structural theorem to scheme surjectivity of `C ×_k T → H`. The published
[`smooth_subgroupProductMap_of_surjective_of_smooth_intersection`](../SubgroupProductSmooth.md)
then proves smoothness of this actual product map. Its proof uses the exact
intersection stabilizer, a cartesian self-pullback comparison, and fpqc
descent, with the arbitrary-field result obtained by field-extension descent.

The provenance is an internal composition of these published proofs and
the published reduction. Both structural premises of the reduction are
discharged; no additional hypothesis remains. The target and its imports
are unchanged. Smoothness or étaleness of the covering map `π` is not
assumed, and its finite central kernel may be nonreduced. Rational-point
openness and valued-field topology remain separate consumer results.
