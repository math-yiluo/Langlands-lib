# Sections over subsets and `c`-soft module sheaves

Author: Worker 61. The module imports Worker 13's `Langlands.Sheaf.CompactSupport`
(`support`, `isClosed_support`, `submodule`, `presheafFunctor`). From Mathlib it uses
topological presheaves and sheaves on `Opens X`, colimits in `ModuleCat`, the fact that
the forgetful functor from modules to types preserves filtered colimits,
`TopCat.Presheaf.Γgerm` (germs of global sections at points),
`TopCat.Sheaf.isProductOfDisjoint`, the flasque class `IsFlasque`, `Retract`, and
`exists_open_between_and_isCompact_closure`.

Composition `f ≫ g` is `f` followed by `g`.

## Setting

All declarations are in the namespace `Langlands.Sheaf.CompactSoft`. `X : TopCat.{u}` is
a topological space and `R : Type u` a commutative ring. Presheaves are
`X.Presheaf (ModuleCat.{u} R)` (presheaves of `R`-modules on the open sets of `X`) and
sheaves are `TopCat.Sheaf (ModuleCat.{u} R) X`, as in `CompactSupport`. No separation or
local compactness hypothesis is used except in `isCSoft_of_isFlasque`. `K`, `L` and `M`
denote arbitrary subsets of `X`.

## Open neighbourhoods of a subset

- `SetNhds K` is the type of open sets `U` with `K ⊆ U`, partially ordered by inclusion
  (`le_def`). It is a meet-semilattice (the meet is the intersection), has the whole
  space as greatest element and is nonempty. As for any preorder, a morphism `U ⟶ V` is
  the inclusion `U ≤ V`.
- `SetNhds.inclusion K : SetNhds K ⥤ Opens X` forgets that the open set contains `K`
  (`inclusion_obj`, `simp`).
- `SetNhds.map h : SetNhds L ⥤ SetNhds K`, for `h : K ⊆ L`, regards a neighbourhood of
  `L` as a neighbourhood of `K`.
- `SetNhds.isTerminalSelf U`: for an open set `U`, `U` itself is the least neighbourhood
  of `U`, so it is a terminal object of the opposite category `(SetNhds U)ᵒᵖ`.

## Sections over a subset

- `setSectionsFunctor R K : X.Presheaf (ModuleCat R) ⥤ ModuleCat R` sends `F` to the
  colimit of `F(U)` over the open neighbourhoods `U` of `K`, with the restriction maps of
  `F` as transition maps. It is the composite of precomposition with
  `(SetNhds.inclusion K).op` and the colimit functor.
- `setSections F K` (an `abbrev`) is `(setSectionsFunctor R K).obj F`. For a sheaf and a
  closed subset with a paracompact neighbourhood, this colimit is Grothendieck's module
  of sections over `K` (see the comparison below); for arbitrary `K` the module is the
  colimit only.
- `setGerm F U hKU : F(U) ⟶ setSections F K`, for an open `U` with `hKU : K ⊆ U`, is the
  colimit insertion: it sends a section over `U` to its germ along `K`.

Lemmas about germs:

- `setGerm_res` (with a `reassoc` form) and `setGerm_res_apply`: for an inclusion
  `i : U ⟶ V` of open sets with `K ⊆ U`, restricting a section from `V` to `U` and then
  taking its germ along `K` gives its germ taken over `V`.
- `exists_setGerm_eq`: every element of `setSections F K` is the germ of a section over
  some open neighbourhood of `K`. The indexing category `(SetNhds K)ᵒᵖ` is filtered
  because `SetNhds K` is a nonempty meet-semilattice, so the forgetful functor to types
  preserves the colimit, and colimit insertions into a colimit of types are jointly
  surjective.
- `setGerm_eq`: if sections `s` over `U` and `t` over `V` have the same germ along `K`,
  there is an open `W ⊇ K` with inclusions into `U` and `V` on which their restrictions
  agree (the description of equality in a filtered colimit of modules).
  `setGerm_ext` is the converse: sections whose restrictions to a common open
  neighbourhood `W` of `K` agree have the same germ.
- `setGerm_naturality` (with a `reassoc` form): for a morphism of presheaves `f : F ⟶ G`,
  `f.app (op U) ≫ setGerm G U hKU = setGerm F U hKU ≫ (setSectionsFunctor R K).map f`.
- `setSections_hom_ext`: two morphisms out of `setSections F K` that agree after every
  germ map are equal.

Restriction to a smaller subset:

- `setSectionsRes F h : setSections F L ⟶ setSections F K`, for `h : K ⊆ L`, is the map of
  colimits induced by `SetNhds.map h`. `setGerm_setSectionsRes` (`simp`, `reassoc`): it
  sends the germ along `L` of a section over `U ⊇ L` to its germ along `K`.
- `setSectionsRes_id`, `setSectionsRes_comp` (restriction along `K ⊆ L` after `L ⊆ M`
  is restriction along `K ⊆ M`) and `setSectionsRes_naturality` (with a `reassoc` form;
  restriction commutes with `(setSectionsFunctor R _).map f`).

Open subsets:

- `isIso_setGerm_self` (instance): for an open set `U`, `setGerm F U _ : F(U) ⟶
  setSections F U` is an isomorphism, since `U` is terminal in the indexing category.
- `openSectionsIso F U : setSections F U ≅ F(U)` is the inverse of this isomorphism.

## Germs of compactly supported sections

`CompactSupport.support F s` is the set of points at which the germ of the global
section `s` is nonzero; it is closed (`CompactSupport.isClosed_support`), and
`CompactSupport.presheafFunctor.obj F` is the module of global sections whose support is
compact.

- `compactGerm F K : CompactSupport.presheafFunctor.obj F ⟶ setSections F K` is the
  inclusion of the compactly supported global sections followed by the germ along `K`
  (`setGerm F ⊤ _`); `compactGerm_apply` states this elementwise, by definition.
- `compactGerm_naturality` (with a `reassoc` form): for `f : F ⟶ G`,
  `CompactSupport.presheafFunctor.map f ≫ compactGerm G K =
  compactGerm F K ≫ (setSectionsFunctor R K).map f`.

## `c`-soft sheaves

- `IsCSoft F`, for a sheaf `F`, means: for every compact subset `K` of `X`,
  `compactGerm F.presheaf K` is surjective. `isCSoft_iff` unfolds this: for every compact
  `K` and every `t` in `setSections F.presheaf K` there is a global section `s` with
  compact support whose germ along `K` is `t`.
- `IsCSoft.of_retract`: if the sheaf `G` is a retract of the `c`-soft sheaf `F` (maps
  `i : G ⟶ F` and `r : F ⟶ G` with `i ≫ r = 𝟙 G`), then `G` is `c`-soft. Given `t` along
  `K`, lift the image of `t` under `i` to a compactly supported section `s` of `F`; then
  `r` applied to `s` has compact support and, by `compactGerm_naturality` and
  `i ≫ r = 𝟙 G`, germ `t`.
- `IsCSoft.of_iso`: `c`-softness is invariant under isomorphism of sheaves (a special
  retract).

### Comparison with Grothendieck's definition

Grothendieck (Tohoku, §3.3, p.159) calls a sheaf of abelian groups `F` *`Φ`-soft*
(`Φ`-mou), for a family `Φ` of closed subsets as in §3.2, if for every `A ∈ Φ` every
section of `F` over `A` is induced by a section `f ∈ Γ_Φ(F)`, i.e. a global section whose
support lies in `Φ`. Here the family `Φ` is the family of compact sets and sections are
`R`-modules, so `Γ_Φ(F)` is `CompactSupport.presheafFunctor.obj F`.

`IsCSoft` replaces Grothendieck's sections over `A`, which are sections of the
restriction of `F` to `A`, by the colimit `setSections F A`. The two agree in the
situation where Grothendieck uses compact supports, a locally compact Hausdorff space:
a compact `K` is then closed and has a compact, hence paracompact, neighbourhood. The
remark on p.159 that every section over a closed set with a paracompact neighbourhood
extends to a neighbourhood gives surjectivity of the map from the colimit to the
sections over `K`, and a section over a neighbourhood whose germs vanish at all points
of `K` vanishes on a smaller neighbourhood, which gives injectivity. This identification
is **not formalized**; the Lean declarations only use the colimit. On spaces that are not
Hausdorff, compact sets need not be closed, so they do not form a family in
Grothendieck's sense; there `IsCSoft` is only the colimit-germ condition stated above.

## Flasque sheaves are `c`-soft

- `exists_glue_zero F h s`: for open sets `V`, `W` with `V ⊓ W = ⊥` and a section `s` over
  `V`, there is a section over `V ⊔ W` that restricts to `s` on `V` and to `0` on `W`.
  Proof: Mathlib's `TopCat.Sheaf.isProductOfDisjoint` exhibits `F(V ⊔ W)` as the product
  of `F(V)` and `F(W)` through the two restriction maps; lift the pair consisting of the
  linear map `R → F(V)`, `r ↦ r • s`, and the zero map `R → F(W)`, and evaluate at `1`.
- `isCSoft_of_isFlasque`: on a locally compact regular space (`[LocallyCompactSpace X]`,
  `[RegularSpace X]`), every flasque sheaf `F` (`[F.IsFlasque]`: all restriction maps are
  epimorphisms) is `c`-soft. Locally compact Hausdorff spaces satisfy both hypotheses.

  Proof. Let `K` be compact and `t` a germ along `K`; by `exists_setGerm_eq`,
  `t = setGerm F U _ s` for a section `s` over an open `U ⊇ K`. By
  `exists_open_between_and_isCompact_closure` there is an open `V` with
  `K ⊆ V`, `closure V ⊆ U` and `closure V` compact. Let `W` be the complement of
  `closure V`, an open set disjoint from `V`. By `exists_glue_zero` there is a section
  `g` over `V ⊔ W` equal to the restriction of `s` on `V` and to `0` on `W`. Since `F` is
  flasque, the restriction from `X` to `V ⊔ W` is an epimorphism of modules, hence
  surjective, so `g` is the restriction of a global section `g'`. At a point outside
  `closure V`, the germ of `g'` factors through the restriction of `g'` to `W`, which is
  `0`; so the support of `g'` is contained in `closure V`. Being closed, the support is
  compact. Finally `g'` and `s` have the same restriction to `V`, so `setGerm_ext` gives
  that the germ of `g'` along `K` is `t`.

Grothendieck states this result on p.159 ("un faisceau flasque de groupes abéliens est
`Φ`-mou pour toute famille `Φ` paracompactifiante"), proved "comme ci-dessus", i.e. by
extending a section near `A`. The written-out argument closest to ours is the proof of
Lemma 3.7.1 2) on pp.172-173, which shows that `f_*` of a flasque sheaf is `Φ`-soft for
paracompactifying `Φ`. It extends the given section over `B ∈ Φ` to an open
neighbourhood, chooses a closed neighbourhood `B₁` of `B` inside it, glues the extended
section on the interior of `B₁` (pulled back by `f`) with `0` on the complement of the
intersection of its support with `f⁻¹(B₁)` (two overlapping open sets, on whose
intersection the section vanishes), extends the glued section by flasqueness, and
checks that its support lies in the support family. With `f` the identity this is the
argument above, except that the Lean proof glues over two disjoint open sets `V` and
`W`.

## Provenance and scope

The definitions are derived ordinary-topological constructions. `setSections` is the
colimit of sections over open neighbourhoods; `IsCSoft` is the colimit form of
Grothendieck's `Φ`-softness for `Φ` the compact sets, with the identification above not
formalized. They are infrastructure for the acyclicity of soft resolutions used for
compactly supported cohomology: Worker 3's argument for the smooth Godement statements
(`Langlands/Cohomology/SmoothGodement/Statement.md`) needs `c`-softness of the Godement
terms and the vanishing of compactly supported cohomology of `c`-soft sheaves.

Not in this module: Lemma 3.3.1 and Proposition 3.3.2 of Tohoku (the abstract
acyclicity lemma and the acyclicity of `Φ`-soft sheaves for paracompactifying `Φ`), the
identification of `setSections` with sections of the restricted sheaf, and the
`c`-softness of the smooth Godement terms. None of them is stated or proved here.

Source: Grothendieck, *Sur quelques points d'algèbre homologique*, Tôhoku Math. J. 9
(1957), §3.3, printed pp.158-159 (one-based PDF pages 40-41: Lemma 3.3.1, definitions of
flasque, soft and `Φ`-soft sheaves, paracompactifying families, flasque implies `Φ`-soft,
Proposition 3.3.2), and §3.7, printed pp.172-173 (one-based PDF pages 54-55: Lemma 3.7.1
and the proof of its part 2)).
Worker 61 read these pages. Source folder
`provided-df60b2162f53c78d858f948959fe779f32064b9b99ef5345277dc18e8008a5f0`, file
`Grothendieck 1957 Tohoku original- acyclic resolutions and derived comparison.pdf`,
SHA-256 `7fb6ca3f5b860361dc75ff6456e25fc7b9e347acb0f08a78a1e032b9c2d330fe`.

Formal dependencies are Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`,
Lean 4.34.0, and the published `Langlands.Sheaf.CompactSupport`. No project axiom,
cohomology output or comparison theorem is an input.
