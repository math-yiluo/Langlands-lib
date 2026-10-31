# Source changes on actual derived categories of étale coefficient diagrams

This module is an internal specialization of `exactDerivedSquareIso` to the
actual associated and constant source-local systems in
`VaryingCoverSourceChange.lean`. It constructs the derived source changes and
proves that the existing invariant-evaluation trivialization commutes with them.
There is no additional source comparison or derived compatibility hypothesis.

## Inputs and categories

Let `X : Scheme.{u}`, `R : Type u` be a commutative ring, and let `I` have object
universe `uI` and morphism universe `vI`. A functor `D : I ⥤ GrpCat.{u}` specifies
the varying groups. The genuine input `Y : EquivariantDiagram D X.Etale` consists
of compatible actions on actual small étale objects over `X`. For associated
coefficients, each action is assumed to be a finite geometric torsor through
`hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i)`. This input has the splitting
meaning documented in `VaryingCoverLocalTrivialization.lean`.

Write `J = X.smallEtaleTopology`. For an arrow `f : k ⟶ l`, the four abelian
categories are:

- the full coefficient category `EquivariantDiagram D (ModuleCat.{u} R)`;
- `Under k ⥤ Sheaf (J.over (Y.obj.obj k)) (ModuleCat.{u} R)`;
- `Under l ⥤ Sheaf (J.over (Y.obj.obj l)) (ModuleCat.{u} R)`;
- the mixed category `Under l ⥤ Sheaf (J.over (Y.obj.obj k)) (ModuleCat.{u} R)`.

The mixed category is essential: both sides of source change must have the same
outgoing-arrow index and the same slice site. The source categories are actual
abelian categories, using the established equivariant-diagram abelian structure
and module sheafification on the actual étale slices. No abelian structure or
exactness of a geometric comparison is added as an assumption.

Chosen `HasDerivedCategory` instances have independent localization morphism
universes `wC`, `wK`, `wL` and `wM`, in the order coefficient, source `k`, source
`l`, mixed. Each derived category is the unbounded quasi-isomorphism localization
of cochain complexes in the **whole diagram category**. It retains all diagram
arrows and naturality, rather than replacing a whole derived diagram by a diagram
of separately derived entries. No enough-injectives or boundedness assumption is
used. The scheme, groups, ring and module carriers share universe `u` as in the
imported geometric coefficient framework.

## Derived restriction, reindexing and source comparison

`etaleSourceRestrictionDerivedFunctor X Y f` is the exact induced functor from
the derived category over source `l` to the mixed derived category. Its ordinary
functor postcomposes the diagram by the actual slice pullback along `Y.obj.map f`.
`etaleSourceReindexDerivedFunctor X Y f` goes from source `k` to the same mixed
category; its ordinary functor precomposes by `Under.map f`, sending an outgoing
arrow `l ⟶ i` to `k ⟶ l ⟶ i`.

Additivity and preservation of finite limits and colimits are supplied by
`SourceSliceExact.lean` and the actual étale site. The functors on derived
categories are constructed with Mathlib's `mapDerivedCategory`; both commute
with integer shifts and are triangulated, using its canonical structures.

`etaleAssociatedSourceDerivedChangeIso` compares association at source `l`
followed by derived restriction with association at source `k` followed by derived
reindexing. `etaleConstantSourceDerivedChangeIso` gives the same comparison for
the underlying coefficient diagram made constant on the original site and then
restricted to the slice. Each is obtained by applying `exactDerivedSquareIso` to
the **constructed ordinary** source-change functor isomorphism. The two derived
comparison morphisms commute with integer shifts.

The ordinary termwise maps still act as the identity on the common actual sheaf
sections at every cochain degree, outgoing-arrow object and slice object. The
two `...complex_hom_f_app_hom_app` lemmas state this directly, without a chosen
derived category assumption.

## Representative and single-degree formulas

For either associated or constant coefficients, write `F` for the source-`l`
ordinary system functor, `G` for source `k`, `P` for restriction, `T` for reindexing,
and `e : F ⋙ P ≅ G ⋙ T` for the ordinary source change. Write `Q` for localization
in the relevant category. The `...hom_app_Q_obj` lemmas identify the derived
comparison at `Q.obj K` with the composite

`Pᴰ(facF.hom) ≫ facP.hom ≫ Q.map (e.hom.mapHomologicalComplex.app K) ≫ facT.inv ≫ Tᴰ(facG.inv)`.

Here each factorization component has exactly the complex argument displayed in
Lean: `facF` and `facG` are evaluated at `K`, while `facP` and `facT` are evaluated
at the termwise images under `F` and `G`. Thus this is the localization of the
actual termwise source change, conjugated by the canonical exact-functor
factorizations.

The `...hom_app_single` lemmas recover the original ordinary source comparison
in **every** integer degree `q`. They use the canonical
`mapDerivedCategorySingleFunctor q` isomorphisms for `F`, `G`, `P` and `T` and the
image of `e.hom.app M` under the mixed category's `singleFunctor`. The imported
`etaleAssociatedSourceChangeFunctorIso_app` and
`etaleConstantSourceChangeFunctorIso_app` identify this ordinary component with
the named objectwise source-change isomorphism. The proofs specialize the generic
representative and single-degree formulas; no recovery equation is supplied as
input.

## Compatibility with invariant evaluation

`etaleAssociatedSourceDerivedTrivialization_sourceChange` proves equality of
natural transformations on the entire derived coefficient category. With `a_l`
and `a_k` the actual associated-to-constant derived trivializations, it states

`whiskerRight a_l.hom Pᴰ ≫ e_constant.hom = e_associated.hom ≫ whiskerRight a_k.hom Tᴰ`.

The proof applies `exactDerivedSquareIso_naturality` to the two ordinary source
comparisons and the **proved ordinary** evaluation square from
`VaryingCoverSourceChange.lean`. The existing derived trivialization is the exact
induced transformation of that same ordinary invariant evaluation. The final
`...sourceChange_app` lemma evaluates this equality at an arbitrary derived
coefficient object. Compatibility holds for all derived objects and morphisms,
including coefficient transitions, rather than only for degree-zero objects.

## Provenance and scope

This is an internal categorical construction from the already implemented actual
étale coefficient functors, source-change maps, exactness and invariant-section
evaluation. The generic localization and square machinery is reused by Lean
name. No new assertion is directly translated from external literature.

The unit treats supplied finite geometric torsors over a supplied scheme. It does
not construct particular Harris geometry, compact-support cohomology,
uniformization, smooth or Galois actions, inverse limits or Ext spectral
sequences. Harris specialization remains a separate implementation step, and the
broad framework task remains incomplete.
