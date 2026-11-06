# Smooth representations on colimit cohomology of level towers of schemes

This internal construction combines the published compatible coefficient
diagrams over varying schemes with the published group action on colimits
over compact open levels. For a tower of schemes indexed by the transporter
category of compact open levels, with étale transition maps and compatible
coefficient sheaves, it forms the colimit over shrinking levels of étale
cohomology. The group acts through the conjugate levels `g K g⁻¹`. It proves
that this action is smooth when every `k ∈ K` acts trivially on level `K`,
both geometrically and on coefficients, and packages the result functorially.
All declarations are in namespace `Langlands.Shimura.LevelTowerCohomology`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, lets the level vary under the action of a finite adelic group: after
(3.5) on printed p. 307 for the prime-to-ℓ finite adeles, and in
Proposition 4.10 on printed p. 311 for `GG(A_f^{ℓ,p})` as `K(N)^{ℓ,p}`
varies. The cohomology of the whole tower, with its smooth action, is the
colimit of the cohomology at finite levels. This module constructs that
colimit for an arbitrary tower satisfying the stated hypotheses. It does not
construct Shimura varieties or Harris's coefficient systems, which are
supplied by other modules. It also gives no Galois action, Hecke-algebra
action, finiteness, compact support or comparison with a limit scheme.

## Inputs

Let `G : Type u` be a group with a topology, and let
`T : CompactOpenLevel G ⥤ Scheme.{u}` be a functor on the published
transporter category of compact open levels, with `Etale (T.map a)` for every
level arrow `a`. Thus an arrow `K ⟶ L`, with element `g` satisfying
`g⁻¹ K g ⊆ L`, gives a scheme map `T K ⟶ T L`; for Shimura towers this is the
right translation by `g`. Let `R : Type u` be a commutative ring.

The coefficients are the published compatible coefficient diagrams
`CoefficientDiagram R T.op` over the scheme diagram `T.op`. They consist of
module sheaves `D.obj (op K)` on the small étale site of `T K` and maps
`D.map a : f_a^*(D.obj (op L)) ⟶ D.obj (op K)` satisfying the published
identity and composition laws, where `f_a = T.map a.unop`. The instance
`etale_op_map` supplies étaleness for `T.op`. The published `D.cohomology q`
is then a functor `(CompactOpenLevel G)ᵒᵖ ⥤ ModuleCat R`, whose map along an
arrow is pullback of cohomology followed by the coefficient map.
`D.sections` is the analogous section diagram.

## Level triviality

- `IsLevelTrivialCoefficients D` states, for every level `K` and `k ∈ K`, that
  the self-arrow `selfArrow K k hk` acts on `T K` by the same scheme morphism
  as the identity arrow. It also requires the coefficient map of the
  self-arrow to equal the identity coefficient map transported along that
  equality by the published `restrictionCongr`.
  `levelTrivialCoefficients T R` is this condition as a property of
  coefficient diagrams.
- `isLevelTrivial_cohomology` states that, under this condition, every
  `D.cohomology q` satisfies the published `LevelColimit.IsLevelTrivial`.
  The proof rewrites the coefficient map, applies the published
  `cohomologyMap_congr` and uses the identity law of the cohomology diagram.
  `isLevelTrivial_sections` deduces the same for `D.sections` through the
  degree-zero identification.

## Colimit representations

Assume moreover that `G` is a topological group.

- `colimitCohomology D q` is `LevelColimit.action (D.cohomology q)`. It is the
  colimit over shrinking levels with the action of `G` through the conjugate
  levels, and needs no level triviality.
- `smoothColimitCohomology D hD q` and `smoothColimitSections D hD` are the
  published `LevelColimit.smoothRep` for cohomology and for sections. They are
  smooth representations of `G` by the previous lemmas.
- `smoothColimitCohomologyFunctor T R q` is the functor from the full
  subcategory of level-trivial coefficient diagrams to smooth
  representations. It lifts the published coefficient-diagram cohomology
  functor into level-trivial presheaves and composes with the published
  `LevelColimit.smoothFunctor`.
- `smoothColimitCohomology_ρ_ι_apply` states the action on a class of level
  `K`. Its image under `g` is the image at level `g K g⁻¹` of the pullback
  along `T.map (conjArrow g K)`, followed by the coefficient map of that
  arrow.
- `exists_level_class` states that, when some compact open level exists,
  every colimit class comes from a single level, by the published
  `LevelColimit.exists_ι_apply`.

## Provenance

This is an internal assembly of the published `CoefficientDiagram`
cohomology over varying schemes, `restrictionCongr` and `cohomologyMap_congr`,
and the published `LevelColimit` action, smoothness and representative
results on the published `CompactOpenLevel` category. Harris's passages are
cited only as motivation; no statement from them is formalized.
