# The locus where a morphism of module sheaves is a stalk isomorphism

Author: Worker 766.

This module is `Langlands.AlgebraicGeometry.Modules.StalkIsoLocus`. All
declarations are in the namespace `Langlands.AlgebraicGeometry.Modules`.

## Purpose and provenance

The module defines the set of points at which a morphism of module sheaves on a
scheme induces a bijection of stalks. It proves that this set is open in two
cases: when both sheaves are locally finitely presented, and when both become
locally finitely presented after pullback along a flat, locally finitely
presented surjection. The second case is the openness step in the proof of
descent of local finite presentation in
`Langlands.AlgebraicGeometry.Modules.FinitePresentationDescent`.

The module is internal. Its results are standard properties of finitely
presented modules and their localizations, written for this development. No
literature theorem is cited.

## Conventions

- `X.Modules` is Mathlib's category of sheaves of modules over the structure
  sheaf of a scheme `X`.
- `stalk M x` and the linear stalk map `stalkMap φ x`, which is linear over the
  local ring of `X` at `x`, come from the Library module
  `Langlands.AlgebraicGeometry.Modules.RelativeFlatness`.
- `stalkFunctor x` is the Library stalk functor
  (`Langlands.AlgebraicGeometry.Modules.StalkAdjunction`) with values in modules
  over the local ring.
- `tilde N` is Mathlib's sheaf on `Spec R` associated to an `R`-module `N`.
  `tilde.toStalk N x` is the localization map from `N` to its stalk at `x`.
  `moduleSpecΓFunctor` is the global sections functor to `R`-modules, and
  `F.fromTildeΓ : tilde Γ(F) ⟶ F` is the counit of the adjunction.

## Declarations

### The iso locus

- `isoLocus φ`, for `φ : M ⟶ N` in `X.Modules`, is the set of points `x` at
  which `stalkMap φ x` is bijective.
- `stalkMap_comp`: the stalk map of a composite is the composite of the stalk
  maps.
- `bijective_stalkMap_of_isIso`: an isomorphism has bijective stalk maps.
- `mem_isoLocus_iff_of_comm`: if `e.hom ≫ φ' = φ ≫ e'.hom` for isomorphisms
  `e` and `e'`, then `φ` and `φ'` have the same iso locus.
- `bijective_stalkMap_iff` and `bijective_stalkMap_iff_isIso_stalkFunctor_map`:
  bijectivity of `stalkMap φ x` is the same as invertibility of the stalk map of
  the underlying abelian presheaves, or of the map in `stalkFunctor x`.
- `isIso_iff_forall_mem_isoLocus`: `φ` is an isomorphism exactly when its iso
  locus is the whole space. This uses the Library criterion
  `Langlands.SchemeModule.isIso_iff_stalk_isIso`.
- `mem_isoLocus_restrict_iff`: for an open immersion `f : W ⟶ X`, a point `w`
  lies in the iso locus of the restriction of `φ` along `f` exactly when `f w`
  lies in the iso locus of `φ`. The proof uses Mathlib's natural isomorphism
  `Scheme.Modules.restrictStalkNatIso`.
- `mem_isoLocus_pullback_iff`: for a flat morphism `p : X ⟶ Y`, a point `x`
  lies in the iso locus of the pullback of `φ` along `p` exactly when `p x`
  lies in the iso locus of `φ`. The stalk of the pullback at `x` is the base
  change of the stalk at `p x` along the local ring map, which is faithfully
  flat (Library `StalkPullback.pullbackStalkIso` and `faithfullyFlat_stalkMap`).
  Base change along a faithfully flat map reflects isomorphisms
  (`ModuleCat.reflectsIsomorphisms_extendScalars_of_faithfullyFlat`).

### Affine spectra

- `stalkMap_tilde_map_toStalk`: for an `R`-linear map `l : A ⟶ B`, the stalk
  map of `tilde.map l` sends the localization of `a` to the localization of
  `l a`.
- `mem_isoLocus_tilde_map_iff`: `x` lies in the iso locus of `tilde.map l`
  exactly when the induced map of localizations at the prime `x`,
  `IsLocalizedModule.map x.asIdeal.primeCompl`, is bijective. Both maps are
  determined by their composites with the localization maps, by
  `IsLocalizedModule.linearMap_ext`.
- `stalkMap_fromTildeΓ_toStalk`: the stalk map of the counit `M.fromTildeΓ`
  sends the localization of a global section `s` to the germ of `s`.
- `mem_isoLocus_iff_tilde_map`: if the counits of `F` and `G` are isomorphisms,
  then `φ : F ⟶ G` and `tilde.map (moduleSpecΓFunctor.map φ)` have the same iso
  locus. This follows from naturality of the counit.
- `exists_basicOpen_subset_isoLocus_tilde`: if `A` is finite and `B` finitely
  presented over `R`, and `x` lies in the iso locus of `tilde.map l`, then some
  `g ∉ x` has its whole basic open `D(g)` in the iso locus. The proof applies
  `Langlands.CommutativeAlgebra.exists_notMem_forall_bijective` to the
  description above.
- `finitePresentation_moduleSpecΓFunctor_of_presentation`: a module sheaf on
  `Spec R` with a finite presentation has finitely presented global sections
  over `R` (Library `finitePresentation_sections_of_presentation` and
  `finitePresentation_moduleSpecΓFunctor`).
- `exists_basicOpen_subset_isoLocus`: let `F` and `G` on `Spec R` have finite
  presentations, and let `x` lie in the iso locus of `φ : F ⟶ G`. Then some
  basic open neighbourhood `D(g)` of `x` lies in the iso locus. The counits of
  `F` and `G` are isomorphisms (Mathlib `isIso_fromTildeΓ_of_presentation`), so
  the previous lemmas apply.

### Presentations on smaller opens

- `presentationRestrictOfFac M g k h hkg P`: given open immersions
  `g : V ⟶ X`, `k : W ⟶ V`, `h : W ⟶ X` with `k ≫ g = h`, a presentation `P`
  of the restriction of `M` along `g` gives a presentation of the restriction of
  `M` along `h`. It restricts `P` along `k` (Mathlib
  `Scheme.Modules.presentationRestrict`) and transports it along the canonical
  isomorphism of restrictions. An instance records that the result is finite
  when `P` is finite.

### Openness

- `isOpen_isoLocus`: if `F` and `G` are locally finitely presented
  (`IsFinitePresentation`), then the iso locus of any `φ : F ⟶ G` is open.
  Given a point `z` in the locus, the Library lemma
  `exists_finitePresentation_restrict` gives opens `U₁` and `U₂` around `z`
  with finite presentations of `F` and `G`. An affine chart `h : Spec R ⟶ X`
  around `z` inside `U₁ ⊓ U₂` carries finite presentations of both restrictions
  (`presentationRestrictOfFac`). By `exists_basicOpen_subset_isoLocus`, the
  image under `h` of a basic open is an open neighbourhood of `z` inside the
  iso locus.
- `isOpen_isoLocus_of_pullback`: let `p : X ⟶ Y` be flat, locally of finite
  presentation and surjective. If the pullbacks of `F` and `G` along `p` are
  locally finitely presented, then the iso locus of any `φ : F ⟶ G` is open. By
  `mem_isoLocus_pullback_iff` and surjectivity, the locus is the image under
  `p` of the iso locus of the pullback of `φ`. That locus is open by
  `isOpen_isoLocus`, and `p` is an open map because it is flat and locally of
  finite presentation (Mathlib's `UniversallyOpen` instance).
