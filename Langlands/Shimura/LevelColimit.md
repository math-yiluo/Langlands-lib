# Group actions on colimits over compact open levels

This internal construction makes a topological group `G` act on the colimit,
over shrinking compact open levels, of any presheaf on the existing category
of levels `CompactOpenLevel G`. An element `g` sends level `K` to the
conjugate level `g K g⁻¹`, using the level arrow `g K g⁻¹ ⟶ K` with element
`g`. For presheaves of modules on which each `k ∈ K` acts trivially at level
`K`, the colimit is proved to be a smooth representation, functorially. The
construction is then applied to the existing level spaces and to the existing
presheaf of forms of all levels.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, defines spaces of forms of a fixed level `K` ((3.1)–(3.3) and (3.7),
printed pp. 307–308). After (3.5) on printed p. 307 he notes: "Letting K vary,
it is clear that these isomorphisms commute with the action of the prime-to-ℓ
finite adeles". The final sentence of Proposition 4.10 on printed p. 311
asserts that its spectral sequences are `GG(A_f^{ℓ,p})`-equivariant as the
level `K(N)^{ℓ,p}` varies, that is, away from both `ℓ` and `p`. Such
statements presuppose a group action on the system of all levels, in which
`g` moves level `K` to `g K g⁻¹`. This module constructs that action on the
colimit over levels for an arbitrary presheaf on the existing level
category, and proves smoothness under the evident level-triviality
condition.

The module does not prove that the transition maps are injective. It does not
identify the colimit with a space of locally constant functions, or prove
admissibility or any finiteness. It constructs no Hecke-algebra action at a
fixed level, and makes no cohomological, Shimura-variety or ℓ-adic
specialization beyond the two applications below. These remain separate
obligations of the broader Harris task.

## Inputs

All declarations are in namespace `Langlands.Shimura`. The existing module
`Langlands.Shimura.Levels` defines `CompactOpenLevel G` for a group `G` with a
topology: an open subgroup `K.openSubgroup` with compact underlying set, with
`K.subgroup` its underlying subgroup. An arrow `a : K ⟶ L` is a group element
`a.element` with `a.element⁻¹ * k * a.element ∈ L.subgroup` for every
`k ∈ K.subgroup`. Composition multiplies elements in order
(`comp_element`), the identity has element `1`, and `inclusion h` is the
arrow with element `1` for an inclusion `h : K.subgroup ≤ L.subgroup`.

## The ordered set of levels and conjugate levels

These declarations are in namespace `Langlands.Shimura.CompactOpenLevel`.

- `Ordered G` is a type synonym for `CompactOpenLevel G`, with the preorder
  `K ≤ L ↔ K.subgroup ≤ L.subgroup` pulled back along `subgroup`.
- `inclusionFunctor : Ordered G ⥤ CompactOpenLevel G` is the identity on
  objects and sends `K ≤ L` to `inclusion`.
- `selfArrow K k hk : K ⟶ K` is the arrow with element `k`, for
  `hk : k ∈ K.subgroup`. `selfArrow_element` records its element.

For a topological group `G`:

- `inf K L` is the level with open subgroup
  `K.openSubgroup ⊓ L.openSubgroup`. Its compactness holds because the
  compact set `K` meets the closed set `L`.
- An instance states that `Ordered G` is directed for `≥`, using `inf`. A
  second instance states that `Ordered G` is cofiltered when some level exists
  (`[Nonempty (CompactOpenLevel G)]`), by Mathlib's
  `isCofiltered_of_directed_ge_nonempty`.
- `conjLevel g K` is the level `g K g⁻¹`. Its open subgroup is the preimage of
  `K.openSubgroup` under `x ↦ g⁻¹ x g`, the same description used for the
  second factor of the existing `heckeLevel K L g = K ∩ g L g⁻¹`. Compactness
  holds because this preimage is the image of `K` under the continuous map
  `y ↦ g y g⁻¹`. `mem_conjLevel` states
  `x ∈ conjLevel g K ↔ g⁻¹ * x * g ∈ K`. This is the conjugate `g K g⁻¹`. The
  existing `CompactOpenLevel.conjugate U g` in
  `Langlands/Shimura/PEL/HarrisTaylorCMConjugationSchemes.lean` is the other
  conjugate `g⁻¹ U g`; this module does not import it.
- `conjArrow g K : conjLevel g K ⟶ K` is the arrow with element `g`.
  `conjArrow_element` records its element.
- `le_conjLevel a` states `K.subgroup ≤ (conjLevel a.element L).subgroup` for
  `a : K ⟶ L`. `conjLevel_mono` states that conjugation preserves inclusions.
- `eq_inclusion_comp_conjArrow a` states that every arrow `a : K ⟶ L` equals
  `inclusion (le_conjLevel a) ≫ conjArrow a.element L`.
- `conjArrow_comp_inclusion` states
  `conjArrow g K ≫ inclusion h = inclusion (conjLevel_mono g h) ≫ conjArrow g L`.
  Both sides have element `g`.

## The colimit and its group action

These declarations are in namespace `Langlands.Shimura.LevelColimit`. Let
`C : Type u` be a category with `Category.{w} C`, let `G : Type v`, and let
`F : (CompactOpenLevel G)ᵒᵖ ⥤ C`.

- `diagram F : (Ordered G)ᵒᵖ ⥤ C` is `inclusionFunctor.op ⋙ F`. When
  `K ≤ L`, its transition map `F L ⟶ F K` is `F.map (inclusion h).op`
  (`diagram_map`). Its colimit is the colimit over shrinking levels.
- `IsLevelTrivial F` is the proposition that
  `F.map (selfArrow K k hk).op = 𝟙 (F.obj (op K))` for every level `K` and
  every `k ∈ K`. `levelTrivialProperty G C` is this proposition as a property
  of objects of `(CompactOpenLevel G)ᵒᵖ ⥤ C`.
- `isLevelTrivial_op_comp T hT E` states that `T.op ⋙ E` is level-trivial for
  any functor `T : CompactOpenLevel G ⥤ D` with `T.map (selfArrow K k hk) = 𝟙`
  and any `E : Dᵒᵖ ⥤ C`.

The remaining declarations assume `[HasColimitsOfShape (Ordered G)ᵒᵖ C]`
explicitly.

- `ι F K : F.obj (op K) ⟶ colimit (diagram F)` is the colimit inclusion of
  level `K`. `map_inclusion_ι` states `F.map (inclusion h).op ≫ ι F K = ι F L`.
  `hom_ext` states that maps out of the colimit agree when they agree after
  every `ι F K`.

For a topological group `G`:

- `translateCocone F g` is the cocone on `diagram F` whose level-`K` leg is
  `F.map (conjArrow g K).op ≫ ι F (conjLevel g K)`. Its naturality,
  `translate_leg_naturality`, follows from `conjArrow_comp_inclusion` and
  `map_inclusion_ι`.
- `translate F g` is the induced endomorphism of the colimit.
  `ι_translate` states
  `ι F K ≫ translate F g = F.map (conjArrow g K).op ≫ ι F (conjLevel g K)`.
- `map_ι a` states, for every arrow `a : K ⟶ L`,
  `F.map a.op ≫ ι F K = ι F L ≫ translate F a.element`. It is proved by
  decomposing `a` with `eq_inclusion_comp_conjArrow`.
- `translate_one` states `translate F 1 = 𝟙`; it is `map_ι` for `𝟙 K`.
  `translate_mul` states
  `translate F (g * h) = translate F h ≫ translate F g`; it is `map_ι` for the
  composite `conjArrow g (conjLevel h L) ≫ conjArrow h L` with element `g * h`.
  Thus `h` acts first, as required for a left action.
- `action F : Action C G` is the colimit with `ρ g = translate F g`
  (`action_V`, `action_ρ`). No level-triviality is needed for the action.
- `ι_translate_of_mem` states that, for a level-trivial `F` and `k ∈ K`,
  `ι F K ≫ translate F k = ι F K`. It is `map_ι` for `selfArrow K k hk`.

Functoriality in the presheaf:

- `map α` is the map of colimits induced by a natural transformation
  `α : F ⟶ F'`, namely `colimMap` of the whiskered transformation.
  `ι_map`, `map_id` and `map_comp` record its formula and functoriality.
  `translate_map` states that `map α` commutes with `translate`; this needs
  only naturality of `α`.
- `functor G C : ((CompactOpenLevel G)ᵒᵖ ⥤ C) ⥤ Action C G` sends `F` to
  `action F` and `α` to `map α` (`functor_obj`, `functor_map_hom`).
- `functorCompForgetIso G C` identifies `functor G C ⋙ Action.forget C G` with
  whiskering by `inclusionFunctor.op` followed by `colim`. Its components are
  identities.

## Smoothness for presheaves of modules

Let `R : Type t` be a commutative ring, `G` a topological group, and assume
`[HasColimitsOfShape (Ordered G)ᵒᵖ (ModuleCat.{w} R)]`. Let
`F : (CompactOpenLevel G)ᵒᵖ ⥤ ModuleCat.{w} R`. `Rep.ActionToRep R G` is the
existing functor presenting a module action as a representation.

- `isSmooth_action F hF` states that, for a level-trivial `F`, the
  representation of `action F` satisfies `Langlands.IsSmooth`: every vector
  is fixed by some open subgroup. Let `S` be the existing submodule
  `smoothVectors` of this representation. Each vector `(ι F K).hom x` lies in
  `S`, being fixed by the open subgroup `K` by `ι_translate_of_mem`. Hence the
  quotient map `S.mkQ` vanishes after every `ι F K`, and `hom_ext` gives
  `S.mkQ = 0`. Therefore `S = ker S.mkQ = ⊤`.
- `translate_ι_apply_of_mem` is the elementwise form of `ι_translate_of_mem`.
  `translate_ι_apply` is the elementwise form of `ι_translate`:
  `(translate F g).hom ((ι F K).hom x)` equals
  `(ι F (conjLevel g K)).hom ((F.map (conjArrow g K).op).hom x)`.
- `exists_ι_apply` states, assuming `[Nonempty (CompactOpenLevel G)]`, that
  every vector of the colimit is `(ι F K).hom y` for some level `K` and some
  `y` of level `K`. No level-triviality is assumed. The set of such vectors is
  a submodule: the sum of vectors from levels `K` and `L` comes from
  `inf K L` by `map_inclusion_ι`, and zero comes from any level. The quotient
  argument above then shows that this submodule is everything. No
  preservation of colimits by a forgetful functor is assumed.
- `smoothRep F hF : SmoothRep.{t, v, w} R G` is the representation of
  `action F`, with `isSmooth_action F hF` as its smoothness proof.
  `smoothRep_ρ_ι_apply` restates `translate_ι_apply` for it.
- `smoothFunctor G R` is the functor from the full subcategory
  `(levelTrivialProperty G (ModuleCat.{w} R)).FullSubcategory` to
  `SmoothRep.{t, v, w} R G`. It lifts the inclusion followed by
  `functor G (ModuleCat.{w} R)` and `Rep.ActionToRep R G` through the full
  subcategory of smooth representations, using `isSmooth_action`.
  `smoothFunctor_obj_obj` states that its underlying representation is
  `(Rep.ActionToRep R G).obj (action F.obj)`.

## Applications

### Level spaces

In namespace `Langlands.Shimura.LevelSpace`, let `ι : Γ →* G` and let `X` be
a `Γ`-set. The existing `LevelSpace ι K` is the double quotient
`Γ \ (X × G) / K`, and `translate g hg` is right translation by `g`.

- `translate_self` states that, for `k ∈ K`, right translation by `k` is the
  identity of `LevelSpace ι K`: `(x, a k)` and `(x, a)` differ by
  `k⁻¹ ∈ K`.
- With topologies on `X` and `G` and continuous multiplication,
  `tower_map_selfArrow` states that the existing level tower
  `tower : CompactOpenLevel G ⥤ TopCat.{max v uX}` sends every `selfArrow` to
  the identity.
- `isLevelTrivial_tower E` states that `tower.op ⋙ E` is level-trivial for
  every `E : TopCat.{max v uX}ᵒᵖ ⥤ C`. For instance, `E` may be a sections or
  cohomology functor on topological spaces; this module constructs no such
  functor.

### Forms of all levels

In namespace `Langlands.Shimura.EquivariantForms`, let `R : Type t`,
`Γ : Type uΓ`, `G : Type v`, `ι : Γ →* G`, and let `ρ` be a representation of
`G` on `V : Type w`. The existing `levelPresheaf R ι ρ` sends a level `K` to
the module `forms ι K.subgroup (ρ.comp K.subgroup.subtype)`. These are
functions `f : G → V` invariant under left translation by `ι Γ` with
`f (x * k) = ρ k⁻¹ (f x)` for `k ∈ K`, the functional equations of Harris
(3.3) and (3.7). An arrow `a : K ⟶ L` acts by
`levelTransport R ι ρ a f = (x ↦ ρ a.element (f (x * a.element)))`.

- `isLevelTrivial_levelPresheaf ι ρ` states that this presheaf is
  level-trivial. For `k ∈ K`, `ρ k (f (x * k)) = ρ k (ρ k⁻¹ (f x)) = f x`.
- For a topological group `G`, `levelColimitRep R ι ρ` is
  `smoothRep (levelPresheaf R ι ρ) (isLevelTrivial_levelPresheaf ι ρ)`, of
  type `SmoothRep.{t, v, max v w} R G`. The colimit exists by Mathlib's
  instances, because `(Ordered G)ᵒᵖ` is small in universe `v` and the module
  carriers lie in `max v w`.
- `levelColimitRep_ρ_ι_apply` states that `g` sends the image of a form `f`
  of level `K` to the image of the form `levelTransport R ι ρ (conjArrow g K) f`
  of level `g K g⁻¹`, that is, `x ↦ ρ g (f (x * g))`.

## Provenance

The constructions are internal assemblies of Mathlib colimits, cocones,
`Action`, `ActionToRep`, full-subcategory lifts and quotient modules over the
existing level category, level spaces, forms presheaf, smooth-vector submodule
and smooth-representation category. Harris's passages cited above are
motivation only; no statement from them is formalized here.
