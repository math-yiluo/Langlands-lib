# Reindexing geometric action diagrams in levels and groups

This internal construction compares actual geometric cohomological action
diagrams after changing their level category and restricting their group.
It uses the actual geometric inverse-image coefficient reindexing from
`EtaleGeometricCoefficientReindex` and the action-valued functors and canonical
recovery maps from `EtaleGeometricActionDiagram`.

The inputs are a commutative ring `R : Type u`, categories `J : Type v` and
`K : Type v'` with morphisms in independent universes `w` and `w'`, groups
`G : Type t` and `H : Type t'`, any functor `F : K ⥤ J`, any monoid
homomorphism `φ : H →* G`, and
`S : (J × SingleObj G) ⥤ Scheme.{u}ᵒᵖ`. Compatible geometric coefficients
`D` consist of actual small-etale module sheaves and coherent inverse-image
coefficient morphisms. Scheme level maps need not be etale and coefficient
transitions need not be invertible. All vertex sheaf categories retain a common
localization universe `wS`, and the module category retains an independent
localization universe `wR`. Ordinary cohomology degrees are nonnegative.

Write `P = F.prod (SingleObj.mapHom H G φ)`. The existing `reindex P D` has
scheme diagram `P ⋙ S`, sheaf `D.obj (F.obj i, star)` at level `i`, and the
original coefficient transition along `P.map a` at every product-index arrow.
This is actual sheaf-level reindexing, before taking cohomology.

The general helper `actionDiagramReindexFunctor F φ C` sends an action-valued
level diagram `A` to `F ⋙ A ⋙ Action.res C φ`. Its construction uses Mathlib's
precomposition, postcomposition and restriction functors. It is available for
arbitrary monoids and an arbitrary category `C : Type uC` with morphisms in
`Type vC`.

`actionDiagramReindexIso F φ E` compares currying of `P ⋙ E` with level
selection and restriction of the action diagram of `E`. Each underlying
component map is the identity on `E.obj (F.obj i, star)`. Equivariance follows
from `F.map_id`: the product-reindexed group arrow has first component
`F.map (𝟙 i)`, which equals `𝟙 (F.obj i)`. Naturality in level arrows follows
from `φ.map_one`. `actionDiagramReindexFunctorIso` proves naturality in all
morphisms of the original product-index diagrams.

`actionDiagramReindexLiftIso` lifts any given natural comparison of
product-index diagrams through `actionDiagramFunctor`. It first postcomposes
that comparison by the action-diagram functor, then precomposes the canonical
`actionDiagramReindexFunctorIso` by the original diagram-valued functor. Its
`_app` theorem records exactly this composite at each input object.

For actual geometric coefficients, the three comparisons are
`reindexDerivedActionIso`, `reindexCohomologyActionIso` and
`reindexSectionsActionIso`. They identify the respective derived-section,
degree-`q` ordinary-cohomology and section action diagrams of `reindex P D`
with `F ⋙ D.derivedAction ⋙ Action.res _ φ`,
`F ⋙ D.cohomologyAction q ⋙ Action.res _ φ` and
`F ⋙ D.sectionsAction ⋙ Action.res _ φ`. The `*_hom_app_hom` lemmas record
the identity underlying components. Their `*FunctorIso` versions are natural
in every compatible coefficient morphism. They apply
`actionDiagramReindexLiftIso` to the already constructed geometric
cohomological reindexing comparisons. The three `*FunctorIso_app` lemmas identify
their components with the specified object comparisons: the supplied
cohomological reindexing comparison has identity components, so its image
under the action-diagram functor is the identity isomorphism.

The comparison maps preserve the specified canonical equivariant recoveries.
With `rD`, `rH` and `rS` denoting the three action-diagram reindex comparisons,
`χq` the existing derived homology comparison, `χ0` the existing derived
comparison with sections and `ε` the existing ordinary degree-zero comparison,
the implemented equations are

```text
mapAction(homology q, H)(rD) ≪≫ restrictφ(F*χq) = χq(reindex P D) ≪≫ rH
mapAction(homology 0, H)(rD) ≪≫ restrictφ(F*χ0) = χ0(reindex P D) ≪≫ rS
rH(q=0) ≪≫ restrictφ(F*ε) = ε(reindex P D) ≪≫ rS.
```

Here `F*` denotes precomposition by `F`, and `restrictφ` denotes
postcomposition by `Action.res`. The typed Lean expressions use
`Functor.isoWhiskerLeft` and `Functor.isoWhiskerRight`; applying homology to
restricted actions and restricting homology actions have the same underlying
objects, action maps and morphisms by their definitions. Each equation is an
equality of full isomorphisms of action-valued diagrams for every compatible
coefficient object. Equations between the two composite natural isomorphisms
on the entire coefficient category are a separate coherence extension; they
are not asserted in this pair.

The recovery proofs use isomorphism, natural-transformation and action-morphism
extensionality. At each vertex they compare the same existing canonical
`homologyNatIso`, `homologyZeroIso` or ordinary degree-zero component, composed
with identities. The functor identity law and category identity laws prove
the resulting equations. No alternative recovery comparison is chosen.

The provenance is internal categorical assembly of the two imported project
constructions with Mathlib's product, currying and action APIs. No desired
cohomology object, action, reindex comparison or recovery law is supplied as an
input. The actions are algebraic actions on derived objects or modules;
realization in the derived category of representations, topological smoothness,
compact supports, tower limits, Galois continuity, arithmetic coefficient
systems and the Harris specialization remain separate obligations.
