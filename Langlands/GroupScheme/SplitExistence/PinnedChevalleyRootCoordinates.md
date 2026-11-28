# Chevalley root coordinates on a supplied split pinning

Fix a split pinning `p : SplitPinning G` over a field and a Chevalley model
`M` of its based root datum. For each of the original root indices `a`,
`SplitPinning.chevalleyRootParametrization` composes the raw additive-group
morphism `M.u a` with the group isomorphism underlying `p.chevalleyIso M`.
The inverse torus square identifies the intrinsic subgroup functors by
`RelativeRoot.subgroup_comap_of_transport`, with characters identified by the
original index. Applying `SubgroupFunctor.IsRepresentedBy.comp_iso` to the
whole model root subgroup gives representability on every test scheme.
The raw root maps are monic closed subgroup embeddings and their
transported maps remain closed. The torus law is transported by first
pulling the torus point back to the model torus and then using the
equality of the corresponding character values.

`SplitPinning.chevalleyRootCoordEquiv` uses `gaRationalEquiv` and the
representability equivalence on field points. It identifies addition of
field coordinates with multiplication in the rational points of the root
subgroup. Its ambient value at a scalar `s` is the image of `M.rootPt a s`
under the pinned group comparison. This is also ordinary evaluation of
the transported root parametrization at `s`.

For a simple root, the differential of the composition takes the model's
standard epsilon vector to the given pinning vector. This uses functoriality
of the differential, the definition of the model pinning vector and its
preservation by the pinned isomorphism. The resulting
`SplitPinning.chevalleyNormalizedRootParametrization` has the unique
normalized morphism by `NormalizedRootParametrization.hom_eq`.

## Sources

- Brian Conrad, *Reductive group schemes* (2014), Definition 6.1.1, p. 186,
  and Theorems 6.1.16(2) and 6.1.17, pp. 196–197.
  `conrad-2014-reductive-group-schemes`, SHA-256
  `1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
  These supply the simple Lie-vector normalization and the comparison of
  based data underlying the transport.
- Robert Steinberg, *Lectures on Chevalley Groups* (2016), Chapter 3,
  pp. 19–22 (PDF pp. 32–35), including Lemmas 15 and 19.
  `steinberg-2016-lectures-chevalley-groups`, SHA-256
  `e3f9ab93111dd88ff3d944a951f4d39b7e08539f6a9b57f22fba0d9bbc19eb89`.
  The root elements use the additive divided-power parameter. Their torus
  conjugation law scales that parameter by the corresponding character.
