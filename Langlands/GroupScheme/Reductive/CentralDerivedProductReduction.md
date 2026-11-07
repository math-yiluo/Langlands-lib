# Central torus and derived subgroup generation: reduction to surjectivity

Worker 1044 wrote the assembly in this module; Worker 1425 wrote the epimorphism
helper `Langlands.AlgebraicGeometry.SurjectiveReducedEpi` that it uses and
packaged the module for submission. It belongs to the proof task
`5dc6c43c-2acc-40a0-92ad-454b4232a509`.

The module proves two conditional results. Neither proves
`Langlands.GroupScheme.ReductiveCentralDerivedProductStatement` outright.

## `reductiveCentralDerivedProduct_of_surjectivity`

This theorem derives `ReductiveCentralDerivedProductStatement.{u}` from two
propositions taken as hypotheses:

- `hrep : DerivedSubgroupRepresentabilityStatement.{u}`, stated in
  `Langlands.GroupScheme.Derived.StructureStatement`. Every affine, locally
  finite-type group scheme over a field has an actual inclusion `d : D ⟶ G`
  with `IsDerivedSubgroup d`.
- `hsurj : ReductiveCentralTorusSurjectivityStatement.{u}`, from
  `Langlands.GroupScheme.Reductive.CentralTorusSurjectivityStatement`. For
  every connected reductive `G` and every `d` with `IsDerivedSubgroup d`,
  there is a closed central affine finite-type torus `i : Z.toGrp ⟶ G` such
  that the underlying map of `subgroupProductMap i d` is surjective.

All three propositions are at the same universe `u`. Neither hypothesis
assumes the target. Representability is a statement about arbitrary affine
finite-type field groups. The surjectivity statement concludes surjectivity on
points, not `Epi`.

The Lean proof fixes a field `k`, a group scheme `G` over `Spec k`, and
`hG : IsConnectedReductive G`.

1. The fields `hG.isAffineHom` and `hG.smooth` of `IsConnectedReductive`
   supply the instances `IsAffineHom G.X.hom` and `Smooth G.X.hom`. Smoothness
   implies `LocallyOfFiniteType G.X.hom` by instance search, which `hrep`
   needs.
2. `hrep k G` gives `D`, `d : D ⟶ G` and `hd : IsDerivedSubgroup d`. The
   affineness and finite-type conjuncts for `D` are discarded, because the
   target does not ask for them.
3. `hsurj k G D d hG hd` gives `Z`, `i`, the five torus conjuncts (affine,
   locally of finite type, torus, closed subgroup, central), and the
   surjectivity `hs` of the underlying function of `(subgroupProductMap i d).left`.
4. `hG.epi_subgroupProductMap_of_surjective i d hs`, from
   `Langlands.AlgebraicGeometry.SurjectiveReducedEpi`, turns `hs` into
   `Epi (subgroupProductMap i d)` in `Over (Spec k)`. A smooth group over a
   field is reduced, and a morphism that is surjective onto a reduced scheme is
   an epimorphism in the category of all schemes, hence in `Over (Spec k)`.
5. The witnesses `Z, D, i, d` and the seven conjuncts are packaged in the
   order the target requires.

## `reductiveCentralDerivedProduct_of_torusSurjectivity`

This entry declaration has type
`ReductiveCentralTorusSurjectivityStatement.{u} → ReductiveCentralDerivedProductStatement.{u}`.
It is a `def` whose type is this implication, with `linter.defProp` disabled,
so that it can be submitted before its hypothesis is proved. It applies the
previous theorem to the Library proof `derivedSubgroupRepresentability`
(module `Langlands.GroupScheme.Derived.RepresentabilityProof`) and to `hsurj`.

## Status and source route

The unconditional proof will apply
`reductiveCentralDerivedProduct_of_torusSurjectivity` to a proof of
`ReductiveCentralTorusSurjectivityStatement`. That proof is the subject of the
separate proof task `5c7bdf70-6574-45e3-88a3-ad60aba3e6d9`, and it carries the
deep structure theory.

The route follows J. S. Milne, *Algebraic Groups* (2017), Proposition 21.61
(printed p.443, PDF p.459), whose step from (b) to (c) reuses 21.60(b) to (c)
(printed p.442, PDF p.458). The radical is a central torus with semisimple
quotient (Corollary 17.62(b),(d)), semisimple groups are perfect (Corollary
21.50), and Proposition 12.46(b) then makes the multiplication map from that
torus times the derived subgroup a quotient map. This module supplies only the
last translation: from surjectivity on points, which the hypothesis provides,
to the scheme-category epimorphism that the target states. Milne's quotient
maps are faithfully flat (5.5/5.7); the Lean argument instead uses that the
target group is reduced, so surjectivity alone suffices.
