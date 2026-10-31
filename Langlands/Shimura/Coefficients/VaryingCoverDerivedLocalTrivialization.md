# Source-local trivialization on actual derived categories

This internal construction prolongs the proved source-local coefficient
trivialization to actual unbounded derived categories. It proves exactness of
the two ordinary functors, constructs their induced triangulated functors and
descends the invariant-evaluation isomorphism through quasi-isomorphism
localization. Explicit formulas retain the original evaluation on cochain
representatives and on coefficients placed in a single degree.

## Inputs and conventions

Fix an actual scheme `X : Scheme.{u}`, a commutative ring `R : Type u`, a
category `I` with independent object and morphism universes `uI` and `vI`,
a group diagram `D : I ⥤ GrpCat.{u}`, and
`Y : EquivariantDiagram D X.Etale`. Require
`hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i)`.
This published predicate requires a finite deck group, a finite, surjective
étale structure map, and a unique deck translation between any two geometric
lifts with the same base map. These properties are hypotheses on supplied
geometry. The coefficient modules are arbitrary; the construction imposes no
finite-generation, smoothness, topology or group-order-invertibility condition.
Scheme, ring, group and module carriers share universe `u`.

Choose a source index `k : I`. Write

```text
J = X.smallEtaleTopology
V = Y.obj.obj k
C = EquivariantDiagram D (ModuleCat.{u} R)
B = Under k ⥤ Sheaf (J.over V) (ModuleCat.{u} R)
F = etaleAssociatedSourceSystemFunctor X Y hY k : C ⥤ B
G = etaleConstantSourceSystemFunctor X Y k : C ⥤ B.
```

An object of `Under k` is an arrow from `k`; its image in `I` is therefore a
cover reachable from the chosen source. `F` restricts the associated sheaf
diagram to these arrows and then to the fixed slice over `V`. `G` forgets the
coefficient actions, restricts the same indices, forms constant sheaves and
restricts to that slice. Both use the actual transitions of their published
ordinary constructions in `VaryingCoverLocalTrivialization.lean`.

The source and target categories are abelian. In the target this uses
`EtaleSlice.moduleHasSheafify`, which constructs module sheafification on the
slice in universe `u` using the equivalence with `V.left`'s own small étale site.
There is no extra sheafification or abelian-structure hypothesis.

The derived section uses independent genuine choices
`HasDerivedCategory.{wC} C` and `HasDerivedCategory.{wS} B`.
These specify Mathlib's actual quasi-isomorphism localizations of all
integer-indexed cochain complexes, with its shift and triangle conventions.
The standard Mathlib choices are available at the maximum object/morphism
universe. There is no boundedness, enough-injectives or derived-smallness
assertion here.

## Ordinary exactness

`etaleSlicePullback_additive` proves additivity of `J.overPullback` on module
sheaves by reducing a sum of morphisms to its components, where both sides are
definitionally the same module map.

`etaleConstantSourceSystemFunctor_additive` obtains additivity from the
components of `G`. Its finite-limit instance uses finite-limit preservation of
the constant-sheaf construction and the already proved exact restriction to a
slice. Its finite-colimit instance uses the constant-sheaf left adjoint
`constantSheafAdj`, evaluated at the actual terminal étale object, and the
left-adjoint slice restriction. Forgetting actions and restricting indices
preserve these shapes by the published equivariant-diagram and Mathlib
functor-category constructions. The proof treats each finite shape separately
so that pointwise right whiskering applies with its required source limits or
colimits.

`etaleAssociatedSourceSystemFunctor_additive` similarly obtains additivity of
`F` from its components. The theorems
`etaleAssociatedSourceSystemFunctorPreservesFiniteLimits` and
`etaleAssociatedSourceSystemFunctorPreservesFiniteColimits` transport the
proved preservation properties of `G` along the already constructed ordinary
isomorphism

```text
e = etaleAssociatedSourceTrivializationFunctor X Y hY k : F ≅ G.
```

Thus exactness and the local trivialization are proved from the supplied torsor
geometry, rather than supplied as comparison fields.

## Derived functors and isomorphism

`etaleAssociatedSourceDerivedFunctor` is `F.mapDerivedCategory` and
`etaleConstantSourceDerivedFunctor` is `G.mapDerivedCategory`. Both commute
with integer shifts and preserve distinguished triangles by Mathlib's exact
functor construction. Their targets are the derived category of the entire
source-local sheaf-diagram category `B`.

`etaleAssociatedSourceDerivedTrivialization`, denoted `eD`, is the natural
isomorphism between these two functors constructed by
`Localization.liftNatIso`. The transformation being lifted is the right
whiskering by `Q_B` of `NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)`.
The source localization is at coefficient quasi-isomorphisms. Exactness
supplies the actual lifting instances for the two derived functors.

The lemma `_hom` identifies `eD.hom` definitionally with
`e.hom.mapDerivedCategory`. Its `NatTrans.CommShift` instance follows from
Mathlib's corresponding instance for that lifted transformation. Naturality of
the isomorphism applies to all derived coefficient morphisms.

## Recovery formulas

For an arbitrary cochain complex `K` in `C`, let
`a_F : Q_C ⋙ Fᴰ ≅ F_complex ⋙ Q_B` and `a_G` be Mathlib's
`mapDerivedCategoryFactors`. The theorem
`etaleAssociatedSourceDerivedTrivialization_hom_app_Q_obj` proves

```text
eD_(Q_C K) = (a_F)_K ≫ Q_B(e_complex,K) ≫ (a_G)_K⁻¹.
```

This is Mathlib's representative formula for the induced natural
transformation, using the definitional identification of `eD.hom`.

The theorem
`etaleAssociatedSourceTrivialization_complex_hom_f_app` states that for every
cochain degree `q : ℤ` and `i : Under k`, the component of `e_complex,K` is

```text
etaleAssociatedEvaluationAlong X Y (K.X q) i.right (Y.obj.map i.hom).
```

This is the actual invariant-section evaluation along the given map from the
source torsor to the cover at `i.right`. Its naturality retains both the
cochain differentials and the reachable-cover transitions.

For a coefficient diagram `M` placed in degree `q`, let
`s_F : single_C(q) ⋙ Fᴰ ≅ F ⋙ single_B(q)` and `s_G` be Mathlib's
`mapDerivedCategorySingleFunctor`. The theorem
`etaleAssociatedSourceDerivedTrivialization_hom_app_single` proves

```text
eD_(single_C(q)(M)) =
  (s_F)_M ≫ single_B(q)(e_M.hom) ≫ (s_G)_M⁻¹.
```

Here `e_M` is precisely the published
`etaleAssociatedSourceTrivialization X Y hY k M`. Both recovery theorems also
have `reassoc` versions.

## Provenance and scope

This is an internal extension of the project constructions in
`VaryingCoverLocalTrivialization.lean`, `VaryingCoverDerived.lean`,
`SliceExact.lean`, `EtaleSlice.lean` and `EquivariantDiagramAbelian.lean`.
The exact and localization constructions use the pinned Mathlib sources
`CategoryTheory/Limits/Preserves/FunctorCategory.lean`,
`CategoryTheory/Sites/ConstantSheaf.lean` and
`Algebra/Homology/DerivedCategory/ExactFunctor.lean`. The new proof route is
finite-shape exactness followed by localization of the already proved
invariant-evaluation isomorphism. No new external-source assertion is made.

This unit constructs derived coefficient objects and maps on supplied genuine
geometry. Actual Harris schemes and their torsors, global or compactly
supported sections, derived inverse limits, smooth and Galois actions,
uniformization and geometric comparison theorems remain separate obligations
of the broad framework and its owned prerequisites.
