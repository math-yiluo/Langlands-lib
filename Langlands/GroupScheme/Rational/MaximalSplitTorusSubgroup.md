# Maximal split tori inside closed subgroup schemes

Author: Worker 1260. Worker 777 identified this bridge in the classification
assembly.

This derived helper works over every field `k : Type u`, with arbitrary
universe `u`. It uses the published predicates `IsSplitSubtorus`,
`IsMaximalSplitTorus`, and `IsClosedSubgroup`, and actual homomorphisms of group
schemes over `Spec k`.

For `i : T.toGrp ⟶ H` and a closed subgroup homomorphism `j : H ⟶ G`:

- `IsSplitSubtorus.comp` composes a split subtorus of `H` with `j` to give a
  split subtorus of `G`.
- `IsSplitSubtorus.of_comp` descends split-subtorus structure from `i ≫ j` to
  `i`. The source torus stays the same; closedness descends by the published
  `IsClosedSubgroup.of_comp`.
- `IsMaximalSplitTorus.of_comp` proves that if `i ≫ j` is maximal split in
  `G`, then `i` is maximal split in `H`. Any factorization of `i` through a
  split subtorus of `H` composes with `j` to give a factorization of `i ≫ j`
  through a split subtorus of `G`. Ambient maximality makes its torus map an
  isomorphism, exactly as required by maximality in `H`.

Suppose a subgroup functor `F` of `G` is represented by `j : H ⟶ G`, with
`IsClosedSubgroup j`. If `i : T.toGrp ⟶ G` is maximal split and
`SubgroupFunctor.range i ≤ F`, the published construction
`hj.factorHom i hcontained` gives its actual lift to `H`.
`IsMaximalSplitTorus.isMaximalSplitTorus_factorHom` applies the preceding
descent result to prove the lift maximal split.
`IsMaximalSplitTorus.lift` bundles that homomorphism with its maximality and
the equality `iH ≫ j = i`; `IsMaximalSplitTorus.exists_lift` exposes the same
data existentially. The containment is an inclusion of subgroup functors on
every test scheme.

For a cocharacter `ν` of `T`, the range of `i` centralizes the whole torus,
hence lies in the dynamic centralizer and parabolic of `groupHom ν ≫ i`.
Consequently, if `P(groupHom ν ≫ i) ≤ P(zeta)`, the theorem
`IsMaximalSplitTorus.exists_lift_of_parabolic_le` lifts `i` to every closed
representative of `P(zeta)` and proves that lift maximal split. The proof
composes these all-test inclusions and applies `exists_lift`. It assumes no
genericity of `ν`, reductivity, smoothness, or connectedness.

The provenance is internal: all results follow from the definitions in
`Rational.SplitTorus`, the closed-subgroup composition in
`Rational.SplitRankTransport`, and the factorization and centralizer lemmas
in `Rational.LeviFactorization`. No additional literature theorem is asserted.
This bridge supports applying maximal-split-torus conjugacy inside a dynamic
parabolic during rational standard-parabolic classification. It proves no
conjugacy theorem and does not discharge either clause of
`StandardParabolicClassificationStatement`.
