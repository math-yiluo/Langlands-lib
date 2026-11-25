# The ordinary neighbourhood system of a point as a germ system on the étale site

This module is a derived helper for a proof of
`AnalyticEtaleGaloisCoinducedLocalAcyclicStatement`. The Library computes the ordinary
germ cohomology `etaleUnderlyingGermCohomology X R y q` with the fiber of the ordinary site
point `underlyingTopologyPoint X y`. The germ functors of
`Langlands.Cohomology.GaloisGerms` are colimits over a small cofiltered index category. This
module writes the neighbourhood system of `y` in that form and identifies the two
constructions, so the Galois–Čech criterion of `Langlands.Cohomology.GaloisCartan` can be
applied to ordinary germ cohomology.

The module imports `Langlands.Cohomology.GaloisGerms` and the Library module
`Langlands.Sheaf.Equivariant.AnalyticOpenEtaleGerms`. All declarations are in the namespace
`Langlands.Sheaf.Equivariant.Analytic`.

## Provenance

The construction and proofs are internal. The underlying fact is standard: the stalk of a
sheaf at a point is the colimit of its sections over the open neighbourhoods of the point.
In Mathlib this colimit is taken over the opposite of the category of elements of the point's
fiber functor (`GrothendieckTopology.Point.presheafFiber`). The objects of that category fit
in the coefficient universe, but its morphism universe comes from the category of opens.
`GaloisGerms` uses an index category with both universes equal to the coefficient universe,
so this module reindexes along the `AsSmall` equivalence, lifting the morphisms to that
universe. Nothing here is a theorem from the literature.

## Setting

The universes are those of the Library: `X : LocalizedCategory.{u, v, v}` over a complete
non-Archimedean field `K : Type u`, the coefficient universe is `w := max u (v + 1) uL`,
`R : Type w` is a commutative ring, and `y : localizedSpaceFunctor.obj X` is a point.

## The neighbourhood system

- `nbhdIndex X y : Type w` is `AsSmall.{w}` of the category of elements of the fiber functor
  of `underlyingTopologyPoint X y`. An object is an open set `U` with a witness of `y ∈ U`.
  A morphism is an inclusion. There are instances `SmallCategory (nbhdIndex X y)` and
  `IsCofiltered (nbhdIndex X y)`. Cofilteredness is transported from the category of
  elements through the `AsSmall` equivalence.
- `nbhdIndex.mk U hy`, for an open `U` and `hy : y ∈ U`, is the corresponding index.
- `nbhdOpen X y : nbhdIndex X y ⥤ Opens (localizedSpaceFunctor.obj X)` returns the open
  set. `nbhdOpen_obj_mk` (simp, by `rfl`) states `(nbhdOpen X y).obj (nbhdIndex.mk U hy) = U`.
  `mem_nbhdOpen X y i` states `y ∈ (nbhdOpen X y).obj i`.
- `nbhdEtale X y := nbhdOpen X y ⋙ openEtaleFunctor X` is the same system as open-domain
  objects of the étale site. `nbhdEtale_obj` (simp, by `rfl`) gives
  `(nbhdEtale X y).obj i = openEtaleObject X ((nbhdOpen X y).obj i)`.
- The instance `nbhdIndex_down_op_final` states that the opposite of `AsSmall.down` is a
  final functor. It is the inverse of an equivalence of categories, hence a right adjoint
  (`Functor.final_of_adjunction`).

## The comparison isomorphism

`germOpenIso X R y` is a natural isomorphism of functors from étale sheaves of `R`-modules:

`etaleUnderlyingSheaf X (ModuleCat R) ⋙ (underlyingTopologyPoint X y).sheafFiber ≅
GaloisGerms.germ (etaleTopology X) R (nbhdEtale X y)`.

Its construction rests on three facts:

- in Mathlib, the sheaf fiber of a point is the forgetful functor to presheaves followed by
  restriction to the category of elements and the colimit;
- the sections of `etaleUnderlyingSheaf X _ F` over an open `U` are definitionally the
  sections of `F` over `openEtaleObject X U` (`etaleUnderlyingSheaf_obj_obj`);
- the colimit is unchanged by precomposition with the final functor `AsSmall.down.op`
  (`Functor.Final.colimIso`).

`germOpenIso_hom_app` records its component at `F` as the inverse of
`Functor.Final.colimitIso` (by `rfl`).

The following lemmas move germs across the isomorphism:

- `toPresheafFiber_germOpenIso_hom` (`@[reassoc (attr := simp)]`): for `i : nbhdIndex X y`,
  the ordinary germ map `toPresheafFiber ((nbhdOpen X y).obj i) ⟨⟨mem_nbhdOpen X y i⟩⟩`
  followed by `(germOpenIso X R y).hom.app F` equals the germ map
  `GaloisGerms.germι (etaleTopology X) R (nbhdEtale X y) F i`;
- `toPresheafFiber_germOpenIso_hom_mk`: the same at an explicit neighbourhood, with
  `toPresheafFiber U ⟨⟨hy⟩⟩` and the index `nbhdIndex.mk U hy`;
- `germι_germOpenIso_inv` (`@[reassoc (attr := simp)]`): the inverse sends the germ map at
  `i` to the ordinary germ map;
- `germOpenIso_hom_app_toPresheafFiber_apply`,
  `germOpenIso_hom_app_toPresheafFiber_mk_apply` and `germOpenIso_inv_app_germι_apply`
  (simp): the same statements applied to a section `s` of `F` over the open-domain object.

## Germ cohomology

`germCohomologyIso X R y q` is an isomorphism

`etaleUnderlyingGermCohomology X R y q ≅
(GaloisGerms.germ (etaleTopology X) R (nbhdEtale X y)).rightDerived q`.

It applies `GaloisCartan.GaloisCechSystem.rightDerivedIsoOfIso` to `germOpenIso X R y`. The
instances are the same terms that `etaleUnderlyingGermCohomology` uses: the Library's
sheafification instances for the étale and ordinary sites, enough injectives on the étale
site, additivity of `etaleUnderlyingSheaf`, and additivity of the sheaf fiber.

## Scope

The module does not construct finite Galois neighbourhoods, germ Galois data or local lifts,
and proves no germ cohomology vanishing. It identifies the ordinary point fiber of the
ordinary direct image with a germ functor along the open neighbourhoods of `y`, and the
corresponding right derived functors.
