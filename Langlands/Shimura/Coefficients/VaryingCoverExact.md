# Exact varying-cover association and canonical diagram homology

Author: Worker 13.

The published varying-cover construction associates an actual diagram of
small-étale module sheaves to a varying-group coefficient diagram. This
module proves finite-limit, finite-colimit and homology preservation for
that functor. It constructs the canonical homology isomorphism for its
existing complex functor, proves compatibility with coefficient chain
maps and cover transitions, and proves preservation of quasi-isomorphisms.

## Provenance

This is an internal categorical derivation from the published
`Langlands.CategoryTheory.EquivariantDiagramAbelian`,
`Langlands.Shimura.Coefficients.EtaleExact`, `VaryingCover`,
`VaryingCoverInverse` and `AssociatedComplex` constructions.
The first supplies the actual abelian coefficient-diagram category and
finite preservation by its action-valued evaluations. `EtaleExact`
supplies exact association on each genuine finite geometric torsor.
Mathlib's pointwise preservation lemmas then give preservation by the
whole diagram functor.

The new homology isomorphism specializes
`Langlands.Cohomology.mapHomologicalComplexHomologyIso` from
`Langlands/Cohomology/DivisibleSystem/InverseLimit.lean`. Only this generic
construction is used; no inverse-limit theorem from that module is
invoked. Mathlib is pinned at
`5ed2965256430c3649e86755f9576b54eca72435`, with the relevant implementations
in `CategoryTheory/Limits/Preserves/FunctorCategory.lean`,
`Algebra/Homology/ShortComplex/PreservesHomology.lean` and
`Algebra/Homology/QuasiIso.lean`. No new result is attributed to Harris
or Berkovich.

## Genuine inputs and universes

The inputs are an actual scheme `X : Scheme.{u}`, a commutative ring
`R : Type u`, an index category `J : Type uJ` with morphisms in universe
`vJ`, an actual group diagram `D : J ⥤ GrpCat.{u}`, and a cover diagram
`Y : EquivariantDiagram D X.Etale`. Scheme, ring, coefficient-module and
group carriers share universe `u` in this specialization. The index
object and morphism universes are independent. For complexes, the
degree type `ι : Type uι` has an independent universe and
`c : ComplexShape ι` is arbitrary.

The explicit hypothesis

```text
hY : ∀ j, IsFiniteGeometricTorsor X (Y.action j)
```

requires a finite deck group at each index, a finite surjective structure
morphism of its actual étale cover, and unique deck translation between
geometric lifts over the same base point. It supplies the hypotheses of
the already proved geometric cover-comparison isomorphisms. The
existing transition is coefficient reduction followed by the inverse
of that proved comparison; no transition or comparison is assumed
as additional input.

No finiteness condition on coefficient modules and no invertibility of
the group orders in `R` is required. There is no topology, continuity or
smoothness hypothesis on the deck actions.

## Finite preservation and the implemented proof

Write

```text
A = EquivariantDiagram D (ModuleCat.{u} R)
S = Sheaf X.smallEtaleTopology (ModuleCat.{u} R)
F = etaleAssociatedVaryingSystemFunctor (R := R) X Y hY :
      A ⥤ (J ⥤ S).
```

For every `j`, the published `etaleAssociatedAt X Y j` is the composite
of action-valued coefficient evaluation at `j` with association on
`Y.action j`. The two theorems
`etaleAssociatedAtPreservesFiniteLimits` and
`etaleAssociatedAtPreservesFiniteColimits` install the corresponding
single-cover certificate using `hY j`, unfold this composite, and use
preservation by both factors.

`etaleAssociatedVaryingEvaluationIso X Y hY j` has type

```text
F ⋙ (evaluation J S).obj j ≅ etaleAssociatedAt X Y j.
```

Its components are identity isomorphisms: the object and morphism
descriptions agree definitionally. Naturality follows from the
identity composition laws.

`etaleAssociatedVaryingSystemFunctorPreservesFiniteLimits` and
`etaleAssociatedVaryingSystemFunctorPreservesFiniteColimits` transport
the at-index preservation certificates through this isomorphism.
Mathlib's `preservesFiniteLimits_of_evaluation` and
`preservesFiniteColimits_of_evaluation` establish preservation by `F`
from those certificates at every index.

The existing functor is additive, as proved in `AssociatedComplex`.
The new `etaleAssociatedVaryingSystemFunctorPreservesHomology` packages
finite preservation as Mathlib's `Functor.PreservesHomology`, which
means preservation of kernels and cokernels. The source is the
published abelian equivariant-diagram category; the target is the
ordinary functor category of module sheaves, with its pointwise
abelian structure.

These preservation results are explicit theorems retaining the torsor
proof `hY`, rather than global instances requiring its silent
inference. A consumer can install a certificate locally, for example
with `have := etaleAssociatedVaryingSystemFunctorPreservesHomology X Y hY`.

## Canonical homology comparison and maps

Let `F_* = etaleAssociatedVaryingComplexFunctor X Y hY c`, the
already constructed prolongation of `F` to complexes. If `Hq` denotes
the categorical homology functor in degree `q`, then
`etaleAssociatedVaryingHomologyIso X Y hY c q` has type

```text
F_* ⋙ Hq_(J ⥤ S) ≅ Hq_A ⋙ F.
```

Its component at `K` is the canonical isomorphism
`Hq(F_*(K)) ≅ F(Hq(K))`. Concretely, it is
`(K.sc q).mapHomologyIso F`, using preserved kernels and cokernels.
The reused generic construction proves its naturality from
`ShortComplex.mapHomologyIso_hom_naturality`.

For a coefficient chain map `f : K ⟶ L`,
`etaleAssociatedVaryingHomologyIso_naturality` exposes the equation

```text
Hq(F_*(f)) ≫ e_L = e_K ≫ F(Hq(f)).
```

Each `e_K` is itself a natural transformation of `J`-diagrams.
For an index arrow `a : i ⟶ j`,
`etaleAssociatedVaryingHomologyIso_transition` exposes its naturality:

```text
(Hq(F_*(K))).map a ≫ (e_K).app j
  = (e_K).app i ≫
      (etaleAssociatedTransition X Y hY a).app (K.homology q).
```

Thus the comparison retains the actual varying-cover transitions.
Both equations have reassociated versions generated by `@[reassoc]`.
Finally, `etaleAssociatedVaryingComplexFunctor_preserves_quasiIso`
uses Mathlib's `HomologicalComplex.quasiIso_map_of_preservesHomology`
with the proved certificate to send a coefficient quasi-isomorphism
to a quasi-isomorphism of associated sheaf-diagram complexes.

## Retained scope

The homology here is ordinary categorical homology in `J ⥤ S`.
The inputs include the actual scheme, covers and coefficient complex.
This module supplies no construction of a Shimura scheme, level tower,
or its finite geometric torsors, and makes no identification of these
inputs with the particular objects of Harris. It does not assert
preservation of infinite limits, exactness of global sections,
compact-support or derived-global-section comparisons, inverse-limit
comparisons, derived completion, or a smooth group or Galois action.
Those specialization and cohomology obligations remain in the broader
framework.
