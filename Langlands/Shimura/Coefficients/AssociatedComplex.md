# Additive associated sheaves and actual associated complexes

Author: Worker 13.

This module proves additivity of the existing associated-sheaf constructions
and uses it to construct ordinary complexes of associated small-etale sheaves.
The input includes the coefficient complex itself; no associated complex,
differential or compatibility theorem is supplied as an assumption.

## Coefficients, sites and universes

`R : Type u` is a commutative ring and coefficients are in `ModuleCat.{u} R`.
For the generic site, `C : Type w` has morphisms in universe `v`, binary
products and a Grothendieck topology `T`. The group carrier has universe `u`.
Only the constant-coefficient construction requires
`HasSheafify T (ModuleCat.{u} R)`.

The small-etale specialization uses an actual scheme `X : Scheme.{u}` and
the topology `X.smallEtaleTopology`. Scheme, ring, coefficient module and
group carriers use the same universe `u` in this specialization. The varying
group index `J : Type uJ` has morphisms in universe `vJ`, and its actual groups
are specified by `D : J ⥤ GrpCat.{u}`. The degree type `ι : Type uι` and
`c : ComplexShape ι` are arbitrary, with independent degree and index
universes. No topology or smoothness condition is imposed on the group actions.

For varying covers, `Y : EquivariantDiagram D X.Etale` is an actual diagram of
cover objects and compatible deck actions. The construction assumes
`hY : ∀ j, IsFiniteGeometricTorsor X (Y.action j)`. This is the existing
predicate requiring a finite group, a finite surjective cover morphism and
unique deck translation between geometric points over a common base point;
the cover object is already etale. The published cover-comparison theorem
then gives the isomorphisms used in the associated-sheaf transitions.
The single-cover construction needs an arbitrary cover action and does not
require this torsor hypothesis.

## Additivity and the implemented proofs

The module supplies the following instances for the published functors.

- `productSheaf_additive` says that restriction to products with the cover
  object, whose sections are `F(Y × U)`, preserves addition of sheaf maps.
  The proof reduces equality first to presheaf natural transformations and
  then to their components, where it is definitional equality.
- `diagonalFunctor_additive` reduces equality of equivariant morphisms to
  their underlying maps and applies product-sheaf additivity. The existing
  diagonal action combines the coefficient action with inverse deck
  pullback; this module preserves that convention.
- `associatedFunctor_additive` proves additivity of the actual invariant
  sheaf functor. It cancels the monic invariant inclusion of the target,
  rewrites all three terms by `inclusion_natural`, and uses bilinearity of
  composition and product-sheaf additivity.
- `constantAssociatedFunctor_additive` and
  `etaleAssociatedFunctor_additive` follow by composition. Mathlib's
  `CategoryTheory.Sites.Abelian` provides constant-sheaf additivity, and
  `Functor.mapAction_preadditive` transports it to actions.
- `etaleAssociatedAt_additive` uses the published additive evaluation
  functor on equivariant diagrams. For
  `etaleAssociatedVaryingSystemFunctor_additive`, equality is reduced to
  each index component and then to the preceding instance.

These are statements about addition on morphisms. No exactness or preservation
of infinite limits is inferred.

## Actual complexes and maps

`etaleAssociatedComplexFunctor X Z c` maps complexes of `G`-module actions to
complexes of small-etale sheaves on `X`, using the single cover action `Z`.
It is the actual prolongation of `etaleAssociatedFunctor X Z`.

For varying groups and covers,
`etaleAssociatedVaryingComplexFunctor X Y hY c` has type

```text
HomologicalComplex (EquivariantDiagram D (ModuleCat R)) c
  ⥤ HomologicalComplex (J ⥤ Sheaf X.smallEtaleTopology (ModuleCat R)) c.
```

Both complex functors are proved additive. They are constructed with
Mathlib's `Functor.mapHomologicalComplex`: the degree object is the associated
sheaf or associated-sheaf diagram, the differential is the associated image of
the input differential, and a chain map is sent degreewise to its associated
map. Preservation of zero morphisms supplies the shape equations, preservation
of composition gives square-zero differentials, and functoriality transports
the chain-map equations.

`etaleAssociatedVaryingComplexSystemFunctor X Y hY c` presents the same
constructed data in the other order, as a `J`-diagram of sheaf complexes.
It composes the preceding functor with Mathlib's
`HomologicalComplex.complexOfFunctorsToFunctorToComplex`.
For an input complex `K`, its complex at `j` has:

- degree `n` equal to
  `(etaleAssociatedFunctor X (Y.action j)).obj ((K.X n).action j)`;
- differential from `p` to `q` equal to the associated image of the
  equivariant map obtained by evaluating `K.d p q` at `j`;
- transition chain map for `a : i ⟶ j` with degree `n` component
  `(etaleAssociatedTransition X Y hY a).app (K.X n)`.

For an input chain map `f`, the degree `n` component at `j` is the associated
image of the evaluation of `f.f n`. The seven named formulas ending in
`_X`, `_d`, `_map_f`, `_obj_X`, `_obj_d`, `_transition_f` and `_map_app_f`
prove these degree, differential, transition and morphism descriptions by
reflexivity. Naturality of the published transition gives its compatibility
with differentials, and its identity and composition laws are retained in
the constructed diagram of complexes.

## Evaluation isomorphism

`etaleAssociatedVaryingComplexEvaluationIso X Y hY c j` is a natural
isomorphism between evaluation at `j` of the constructed complex-system
functor and `(etaleAssociatedAt X Y j).mapHomologicalComplex c`.
Their objects and differentials agree definitionally. Each isomorphism
component is `Iso.refl`; naturality is proved degreewise by the identity
composition laws. This compares two presentations of the same associated
complex, without introducing an additional sheaf comparison theorem.

## Provenance and retained scope

This is internally derived infrastructure. The actual invariant-sheaf,
constant-coefficient, etale and varying-cover constructions come from the
published modules `Associated`, `Etale`, `VaryingCover` and
`VaryingCoverInverse` in this directory. The additive structure and evaluation
on coefficient diagrams come from
`Langlands.CategoryTheory.EquivariantDiagramPreadditive`.
Mathlib at the project's pinned revision
`5ed2965256430c3649e86755f9576b54eca72435` supplies the sheaf and action
additivity instances and the complex constructions in
`CategoryTheory.Sites.Abelian`, `CategoryTheory.Action.Limits`,
`Algebra.Homology.Additive` and `Algebra.Homology.Functor`.
No new theorem is attributed to Harris or Berkovich.

The scope is ordinary associated complexes with actual differentials,
chain maps and varying-cover transitions. Exactness, cohomology, derived
functors, completion comparisons, smoothness, and identification with the
particular coefficient objects in Harris remain separate obligations.
