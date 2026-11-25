/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.LimitsOver
public import Mathlib.AlgebraicGeometry.Morphisms.LocalIso
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.FullyFaithful

/-!
# The essential image of base change along a universal homeomorphism is local

Let `f : X ⟶ Y` be a universal homeomorphism. We show that an étale `X`-scheme `U` lies in the
essential image of `f.Etale : Y.Etale ⥤ X.Etale` as soon as every point of `U` has an open
neighbourhood which does (`AlgebraicGeometry.Scheme.Hom.etale_essImage_of_forall_exists_mem`).
This is the gluing step in the proof of the topological invariance of the small étale site,
[Stacks 04DZ].

## Main statements

- `AlgebraicGeometry.IsOpenImmersion.of_etale_of_universallyInjective`: an étale universally
  injective morphism is an open immersion.
- `AlgebraicGeometry.IsOpenImmersion.of_isLocalIso_of_injective`: a local isomorphism which is
  injective on points is an open immersion.
- `AlgebraicGeometry.Scheme.Hom.etale_essImage_restrict`,
  `AlgebraicGeometry.Scheme.Hom.etale_essImage_of_le`: the essential image of `f.Etale` is
  closed under passing to open subschemes.
- `AlgebraicGeometry.Scheme.Hom.isPullback_etale_map_left`: the base change square of a
  morphism of étale `Y`-schemes along `f` is cartesian.
- `AlgebraicGeometry.Scheme.Hom.etale_essImage_of_forall_exists_mem`: the essential image of
  `f.Etale` is local on the étale `X`-scheme.

## Proof sketch

Let `J` be the set of open subschemes `W ⊆ U` lying in the essential image, ordered by
inclusion; it is a lower set, in particular closed under intersections. For every `W : J` we
choose an étale `Y`-scheme `V W` with `V W ×_Y X ≅ W`. Full faithfulness of `f.Etale` upgrades
the inclusions `W ⊆ W'` to a diagram `F : J ⥤ Y.Etale` whose transition maps are open
immersions (they are étale and their base changes are open immersions, and universal
injectivity descends along surjections). The points of `V W` correspond to the points of `W`
via the homeomorphism `V W ×_Y X ⟶ V W`, compatibly with the transition maps; this identifies
`F` as a locally directed diagram of open immersions, so its colimit `V` exists in `Y.Etale` and
is covered by the open subschemes `V W` (`Mathlib.AlgebraicGeometry.LimitsOver`).

The maps `W ≅ V W ×_Y X ⟶ V ×_Y X` glue to an `X`-morphism `θ : U ⟶ V ×_Y X`, which is a
local isomorphism, injective (by the description of the points of the colimit) and surjective,
hence an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- An étale, universally injective morphism is an open immersion. -/
lemma IsOpenImmersion.of_etale_of_universallyInjective {X Y : Scheme.{u}} (g : X ⟶ Y)
    [Etale g] [UniversallyInjective g] : IsOpenImmersion g := by
  have hmono : Mono g := by
    rw [← pullback.isIso_diagonal_iff]
    have : Surjective (pullback.diagonal g) := (UniversallyInjective.iff_diagonal g).mp ‹_›
    exact isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by ext1; simp)
  exact IsOpenImmersion.of_flat_of_mono g

/-- A local isomorphism which is injective on points is an open immersion. -/
lemma IsOpenImmersion.of_isLocalIso_of_injective {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsLocalIso g] (hg : Function.Injective g.base) : IsOpenImmersion g := by
  have hle : @IsLocalIso ≤ @Etale := IsLocalIso.le_of_isZariskiLocalAtSource _
  have : Etale g := hle _ _ g ‹_›
  have hopen : IsOpenMap g.base := g.isOpenMap
  have : ∀ x, IsIso (g.stalkMap x) := by
    intro x
    obtain ⟨U, hxU, hU⟩ := IsLocalIso.exists_isOpenImmersion (f := g) x
    have hx : x = U.ι ⟨x, hxU⟩ := rfl
    have := Scheme.Hom.stalkMap_comp U.ι g ⟨x, hxU⟩
    rw [hx]
    exact IsIso.of_isIso_fac_right this.symm
  exact IsOpenImmersion.of_isIso_stalkMap g
    (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap g.continuous hg hopen)

namespace Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsUniversalHomeomorphism f]

set_option backward.isDefEq.respectTransparency false in
/-- Open subschemes of étale `X`-schemes in the essential image of base change along a
universal homeomorphism are again in the essential image: the open subscheme corresponds, via
the homeomorphism `V ×_Y X ⟶ V`, to an open subscheme of `V`, whose base change it is. -/
lemma etale_essImage_restrict {U : X.Etale} (hU : f.Etale.essImage U) (W : U.left.Opens) :
    f.Etale.essImage (Etale.mk (W.ι ≫ U.hom)) := by
  obtain ⟨V, ⟨e⟩⟩ := hU
  let h : pullback V.hom f ⟶ V.left := pullback.fst V.hom f
  have hh : IsHomeomorph h.base := h.isHomeomorph
  let W' : (pullback V.hom f).Opens := e.hom.left ⁻¹ᵁ W
  let O : V.left.Opens := ⟨h.base '' W', hh.isOpenMap _ W'.isOpen⟩
  let V' : Y.Etale := Etale.mk (O.ι ≫ V.hom)
  refine ⟨V', ⟨MorphismProperty.Over.isoMk ?_ ?_⟩⟩
  · refine (pullbackRightPullbackFstIso V.hom f O.ι).symm ≪≫
      IsOpenImmersion.isoOfRangeEq (pullback.snd O.ι h) W'.ι ?_ ≪≫
      IsOpenImmersion.isoOfRangeEq (W'.ι ≫ e.hom.left) W.ι ?_
    · rw [Scheme.Pullback.range_snd, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
      exact Set.preimage_image_eq _ hh.injective
    · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
      change e.hom.left.base '' (e.hom.left.base ⁻¹' W) = Set.range W.ι.base
      have hs : Function.Surjective e.hom.left.base := e.hom.left.homeomorph.surjective
      rw [Set.image_preimage_eq _ hs, Scheme.Opens.range_ι]
  · simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    change _ ≫ _ ≫ _ ≫ W.ι ≫ U.hom = pullback.snd (O.ι ≫ V.hom) f
    rw [IsOpenImmersion.isoOfRangeEq_hom_fac_assoc, Category.assoc,
      IsOpenImmersion.isoOfRangeEq_hom_fac_assoc]
    have : e.hom.left ≫ U.hom = pullback.snd V.hom f := MorphismProperty.Over.w e.hom
    rw [this, pullbackRightPullbackFstIso_inv_snd_snd]

set_option backward.isDefEq.respectTransparency false in
/-- The essential image of base change along a universal homeomorphism is closed under passing
to smaller open subschemes. -/
lemma etale_essImage_of_le {U : X.Etale} {W W' : U.left.Opens}
    (hW : f.Etale.essImage (Etale.mk (W.ι ≫ U.hom))) (h : W' ≤ W) :
    f.Etale.essImage (Etale.mk (W'.ι ≫ U.hom)) := by
  have hrange : Set.range ((W.ι ⁻¹ᵁ W').ι ≫ W.ι).base = Set.range W'.ι.base := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
      Scheme.Opens.range_ι]
    change W.ι.base '' (W.ι.base ⁻¹' W') = W'
    rw [Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
    exact Set.inter_eq_left.mpr h
  exact (etale_essImage_restrict f hW (W.ι ⁻¹ᵁ W')).ofIso (MorphismProperty.Over.isoMk
    (IsOpenImmersion.isoOfRangeEq ((W.ι ⁻¹ᵁ W').ι ≫ W.ι) W'.ι hrange) (by simp))

omit [IsUniversalHomeomorphism f] in
set_option backward.isDefEq.respectTransparency false in
/-- The square

```
   A ×_Y X ──(f.Etale.map g).left──→ B ×_Y X
      │                                 │
      │ pullback.fst A.hom f            │ pullback.fst B.hom f
      ↓                                 ↓
      A ────────────g.left────────────→  B
```

is cartesian. -/
lemma isPullback_etale_map_left {A B : Y.Etale} (g : A ⟶ B) :
    IsPullback (f.Etale.map g).left (pullback.fst A.hom f) (pullback.fst B.hom f) g.left := by
  refine IsPullback.of_right (h₁₂ := pullback.snd B.hom f) (v₁₃ := f) (h₂₂ := B.hom) ?_
    (etale_map_left_comp_fst f g) (IsPullback.of_hasPullback B.hom f).flip
  have h₁ : (f.Etale.map g).left ≫ pullback.snd B.hom f = pullback.snd A.hom f :=
    MorphismProperty.Over.w (f.Etale.map g)
  have h₂ : g.left ≫ B.hom = A.hom := MorphismProperty.Over.w g
  rw [h₁, h₂]
  exact (IsPullback.of_hasPullback A.hom f).flip

namespace EtaleEssImageGluing

variable (U : X.Etale)

/-- The index set of the gluing: the open subschemes of `U` which lie in the essential image of
base change along `f`, ordered by inclusion. -/
def Idx : Type u := {W : U.left.Opens // f.Etale.essImage (Etale.mk (W.ι ≫ U.hom))}

instance : PartialOrder (Idx f U) := Subtype.partialOrder _

instance : Category (Idx f U) := Preorder.smallCategory _

instance : Quiver.IsThin (Idx f U) := fun _ _ ↦ inferInstanceAs (Subsingleton (ULift _))

/-- The open subscheme `W` of `U`, as an étale `X`-scheme. -/
abbrev obj (W : Idx f U) : X.Etale := Etale.mk (W.1.ι ≫ U.hom)

/-- A chosen étale `Y`-scheme whose base change is `W`. -/
noncomputable def V (W : Idx f U) : Y.Etale := W.2.witness

/-- The chosen isomorphism between the base change of `V W` and `W`. -/
noncomputable def e (W : Idx f U) : f.Etale.obj (V f U W) ≅ obj f U W := W.2.getIso

/-- The inclusion of open subschemes as a morphism of étale `X`-schemes. -/
noncomputable def incl {W W' : Idx f U} (g : W ⟶ W') : obj f U W ⟶ obj f U W' :=
  MorphismProperty.Over.homMk (U.left.homOfLE (leOfHom g)) (by simp)

omit [IsUniversalHomeomorphism f] in
@[simp]
lemma incl_left {W W' : Idx f U} (g : W ⟶ W') :
    (incl f U g).left = U.left.homOfLE (leOfHom g) := rfl

/-- The diagram of the chosen descents `V W`, with transition maps obtained from full
faithfulness of base change. -/
noncomputable def F : Idx f U ⥤ MorphismProperty.Over @AlgebraicGeometry.Etale ⊤ Y where
  obj := V f U
  map {W W'} g := f.Etale.preimage ((e f U W).hom ≫ incl f U g ≫ (e f U W').inv)
  map_id W := f.Etale.map_injective (by
    rw [Functor.map_preimage, CategoryTheory.Functor.map_id]
    have : incl f U (𝟙 W) = 𝟙 _ := by apply MorphismProperty.Over.Hom.ext; simp; rfl
    rw [this, Category.id_comp, Iso.hom_inv_id])
  map_comp {W W' W''} g g' := f.Etale.map_injective (by
    rw [Functor.map_preimage, Functor.map_comp, Functor.map_preimage, Functor.map_preimage]
    have : incl f U (g ≫ g') = incl f U g ≫ incl f U g' := by
      apply MorphismProperty.Over.Hom.ext
      rw [MorphismProperty.Comma.comp_left, incl_left, incl_left, incl_left, Scheme.homOfLE_homOfLE]
    rw [this]
    simp)

lemma map_F_map {W W' : Idx f U} (g : W ⟶ W') :
    f.Etale.map ((F f U).map g) = (e f U W).hom ≫ incl f U g ≫ (e f U W').inv :=
  Functor.map_preimage _ _

omit [IsUniversalHomeomorphism f] in
instance {A B : X.Etale} (i : A ≅ B) : IsIso i.hom.left :=
  inferInstanceAs (IsIso i.hom.hom.left)

omit [IsUniversalHomeomorphism f] in
instance {A B : X.Etale} (i : A ≅ B) : IsIso i.inv.left :=
  inferInstanceAs (IsIso i.inv.hom.left)

/-- The base change of a transition map is an open immersion. -/
instance {W W' : Idx f U} (g : W ⟶ W') : IsOpenImmersion (f.Etale.map ((F f U).map g)).left := by
  rw [map_F_map, MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left, incl_left]
  infer_instance

/-- The transition maps are open immersions. -/
instance {W W' : Idx f U} (g : W ⟶ W') : IsOpenImmersion ((F f U).map g).left := by
  have hsq := isPullback_etale_map_left f ((F f U).map g)
  have : MorphismProperty.DescendsAlong @UniversallyInjective @Surjective :=
    universallyInjective_eq_diagonal ▸ inferInstance
  have : UniversallyInjective ((F f U).map g).left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyInjective)
      (Q := @Surjective) hsq inferInstance inferInstance
  exact IsOpenImmersion.of_etale_of_universallyInjective _

/-- The homeomorphism `V W ×_Y X ≃ₜ V W` induced by the universal homeomorphism `f`. -/
noncomputable abbrev homeo (W : Idx f U) :
    ((pullback (V f U W).hom f : Scheme.{u}) : Type u) ≃ₜ ((V f U W).left : Type u) :=
  IsUniversalHomeomorphism.homeomorph (pullback.fst (V f U W).hom f)

lemma homeo_apply (W : Idx f U) (y : (pullback (V f U W).hom f : Scheme.{u})) :
    homeo f U W y = pullback.fst (V f U W).hom f y := rfl

lemma homeo_symm_fst (W : Idx f U) (y : (pullback (V f U W).hom f : Scheme.{u})) :
    (homeo f U W).symm (pullback.fst (V f U W).hom f y) = y :=
  (homeo f U W).symm_apply_apply y

/-- The identification of the points of `V W` with the points of `W ⊆ U`. -/
noncomputable def pt (W : Idx f U) (x : (V f U W).left) : U.left :=
  W.1.ι ((e f U W).hom.left ((homeo f U W).symm x))

lemma pt_injective (W : Idx f U) : Function.Injective (pt f U W) := by
  intro x y h
  have := W.1.ι.isOpenEmbedding.injective h
  have := (e f U W).hom.left.homeomorph.injective this
  exact (homeo f U W).symm.injective this

lemma range_pt (W : Idx f U) : Set.range (pt f U W) = W.1 := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [← Scheme.Opens.range_ι]
    exact ⟨_, rfl⟩
  · intro u hu
    refine ⟨homeo f U W ((e f U W).hom.left.homeomorph.symm ⟨u, hu⟩), ?_⟩
    have h := (e f U W).hom.left.homeomorph.apply_symm_apply ⟨u, hu⟩
    rw [Scheme.Hom.homeomorph_apply] at h
    change W.1.ι ((e f U W).hom.left ((homeo f U W).symm (homeo f U W _))) = u
    rw [Homeomorph.symm_apply_apply, h]
    rfl

lemma pt_map {W W' : Idx f U} (g : W ⟶ W') (x : (V f U W).left) :
    pt f U W' (((F f U).map g).left x) = pt f U W x := by
  obtain ⟨y, rfl⟩ := (homeo f U W).surjective x
  have h1 : ((F f U).map g).left (homeo f U W y) =
      pullback.fst (V f U W').hom f ((f.Etale.map ((F f U).map g)).left y) := by
    change (pullback.fst (V f U W).hom f ≫ ((F f U).map g).left) y =
      ((f.Etale.map ((F f U).map g)).left ≫ pullback.fst (V f U W').hom f) y
    exact (congrArg (fun φ ↦ φ y) (etale_map_left_comp_fst f ((F f U).map g))).symm
  rw [h1]
  simp only [pt, homeo_symm_fst, Homeomorph.symm_apply_apply]
  have h : f.Etale.map ((F f U).map g) ≫ (e f U W').hom = (e f U W).hom ≫ incl f U g := by
    rw [map_F_map, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h2 : (e f U W').hom.left ((f.Etale.map ((F f U).map g)).left y) =
      U.left.homOfLE (leOfHom g) ((e f U W).hom.left y) := by
    change ((f.Etale.map ((F f U).map g)) ≫ (e f U W').hom).left y =
      ((e f U W).hom ≫ incl f U g).left y
    rw [h]
    rfl
  rw [h2]
  change (U.left.homOfLE (leOfHom g) ≫ W'.1.ι) _ = _
  rw [Scheme.homOfLE_ι]

/-- The intersection of two indices. -/
def inf (i j : Idx f U) : Idx f U :=
  ⟨i.1 ⊓ j.1, etale_essImage_of_le f i.2 inf_le_left⟩

lemma inf_le_left (i j : Idx f U) : inf f U i j ≤ i := _root_.inf_le_left (a := i.1) (b := j.1)

lemma inf_le_right (i j : Idx f U) : inf f U i j ≤ j := _root_.inf_le_right (a := i.1) (b := j.1)

/-- The diagram of the `V W` is locally directed: the points of `V W` are the points of `W`,
and the intersection of two indices is again an index. -/
instance isLocallyDirected :
    (F f U ⋙ MorphismProperty.Over.forget _ ⊤ Y ⋙ Over.forget Y ⋙
      Scheme.forget).IsLocallyDirected where
  cond {i j k} fi fj xi xj hx := by
    change ((F f U).map fi).left xi = ((F f U).map fj).left xj at hx
    have hu : pt f U i xi = pt f U j xj := by
      rw [← pt_map f U fi xi, ← pt_map f U fj xj, hx]
    obtain ⟨x, hx'⟩ : pt f U i xi ∈ Set.range (pt f U (inf f U i j)) := by
      rw [range_pt]
      refine ⟨?_, ?_⟩
      · rw [← range_pt f U i]; exact ⟨xi, rfl⟩
      · rw [hu, ← range_pt f U j]; exact ⟨xj, rfl⟩
    refine ⟨inf f U i j, homOfLE (inf_le_left f U i j), homOfLE (inf_le_right f U i j), x, ?_, ?_⟩
    · apply pt_injective f U i
      change pt f U i (((F f U).map _).left x) = _
      rw [pt_map, hx']
    · apply pt_injective f U j
      change pt f U j (((F f U).map _).left x) = _
      rw [pt_map, hx', hu]



section Colimit

/-- The underlying diagram of schemes. -/
noncomputable abbrev G : Idx f U ⥤ Scheme.{u} :=
  F f U ⋙ MorphismProperty.Over.forget _ ⊤ Y ⋙ Over.forget Y

instance {W W' : Idx f U} (g : W ⟶ W') : IsOpenImmersion ((G f U).map g) :=
  inferInstanceAs (IsOpenImmersion ((F f U).map g).left)

instance : (G f U ⋙ Scheme.forget).IsLocallyDirected := isLocallyDirected f U

/-- The glued étale `Y`-scheme. -/
noncomputable abbrev glued : MorphismProperty.Over @AlgebraicGeometry.Etale ⊤ Y := colimit (F f U)

/-- The structure maps into the glued scheme. -/
noncomputable abbrev ι (W : Idx f U) : (F f U).obj W ⟶ glued f U := colimit.ι (F f U) W

/-- The underlying scheme of the glued étale `Y`-scheme is the colimit of the underlying
diagram of schemes. -/
noncomputable abbrev gluedIso : (glued f U).left ≅ colimit (G f U) :=
  preservesColimitIso (MorphismProperty.Over.forget _ ⊤ Y ⋙ Over.forget Y) (F f U)

lemma ι_left_gluedIso_hom (W : Idx f U) :
    (ι f U W).left ≫ (gluedIso f U).hom = colimit.ι (G f U) W :=
  ι_preservesColimitIso_hom (MorphismProperty.Over.forget _ ⊤ Y ⋙ Over.forget Y) (F f U) W

lemma exists_ι_left_eq (v : (glued f U).left) : ∃ (W : Idx f U) (x : (V f U W).left),
    (ι f U W).left x = v := by
  obtain ⟨W, x, hx⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (G f U) ((gluedIso f U).hom v)
  refine ⟨W, x, (gluedIso f U).hom.homeomorph.injective ?_⟩
  rw [Scheme.Hom.homeomorph_apply, Scheme.Hom.homeomorph_apply, ← hx, ← ι_left_gluedIso_hom,
    Scheme.Hom.comp_apply]
  rfl

lemma ι_left_eq_iff {W W' : Idx f U} (x : (V f U W).left) (x' : (V f U W').left) :
    (ι f U W).left x = (ι f U W').left x' ↔
      ∃ (l : Idx f U) (g : l ⟶ W) (g' : l ⟶ W') (y : (V f U l).left),
        ((F f U).map g).left y = x ∧ ((F f U).map g').left y = x' := by
  rw [← (gluedIso f U).hom.homeomorph.injective.eq_iff, Scheme.Hom.homeomorph_apply,
    Scheme.Hom.homeomorph_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
    ι_left_gluedIso_hom, ι_left_gluedIso_hom]
  exact Scheme.IsLocallyDirected.ι_eq_ι_iff (G f U)

end Colimit

section Glue

/-- The map `W ⟶ glued ×_Y X` for an index `W`, obtained from the chosen isomorphism
`V W ×_Y X ≅ W` and the base change of the structure map `V W ⟶ glued`. -/
noncomputable def θW (W : Idx f U) : (W.1 : Scheme.{u}) ⟶ pullback (glued f U).hom f :=
  (e f U W).inv.left ≫ (f.Etale.map (ι f U W)).left

instance (W : Idx f U) : IsOpenImmersion (θW f U W) := by
  have : IsOpenImmersion (f.Etale.map (ι f U W)).left :=
    MorphismProperty.of_isPullback (isPullback_etale_map_left f (ι f U W)).flip inferInstance
  unfold θW
  infer_instance

lemma homOfLE_θW {W W' : Idx f U} (g : W ⟶ W') :
    U.left.homOfLE (leOfHom g) ≫ θW f U W' = θW f U W := by
  unfold θW
  have hw : f.Etale.map (ι f U W) =
      f.Etale.map ((F f U).map g) ≫ f.Etale.map (ι f U W') := by
    rw [← Functor.map_comp]
    exact congrArg _ (colimit.w (F f U) g).symm
  rw [hw, MorphismProperty.Comma.comp_left, map_F_map, MorphismProperty.Comma.comp_left,
    MorphismProperty.Comma.comp_left, incl_left]
  have : (e f U W).inv.left ≫ (e f U W).hom.left = 𝟙 (W.1 : Scheme.{u}) := by
    rw [← MorphismProperty.Comma.comp_left, Iso.inv_hom_id]; rfl
  simp only [← Category.assoc, this, Category.id_comp]

lemma θW_compat (i j : Idx f U) :
    pullback.fst i.1.ι j.1.ι ≫ θW f U i = pullback.snd i.1.ι j.1.ι ≫ θW f U j := by
  have hr : Set.range (pullback.fst i.1.ι j.1.ι ≫ i.1.ι).base ⊆
      Set.range (inf f U i j).1.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← Scheme.Opens.range_ι]
      exact ⟨_, rfl⟩
    · rw [← Scheme.Opens.range_ι, pullback.condition]
      exact ⟨_, rfl⟩
  let π := IsOpenImmersion.lift (inf f U i j).1.ι (pullback.fst _ _ ≫ i.1.ι) hr
  have hπ : π ≫ (inf f U i j).1.ι = pullback.fst _ _ ≫ i.1.ι := IsOpenImmersion.lift_fac _ _ _
  have h1 : pullback.fst i.1.ι j.1.ι = π ≫ U.left.homOfLE (inf_le_left f U i j) := by
    rw [← cancel_mono i.1.ι, Category.assoc, Scheme.homOfLE_ι, hπ]
  have h2 : pullback.snd i.1.ι j.1.ι = π ≫ U.left.homOfLE (inf_le_right f U i j) := by
    rw [← cancel_mono j.1.ι, Category.assoc, Scheme.homOfLE_ι, hπ, pullback.condition]
  rw [h1, h2, Category.assoc, Category.assoc, homOfLE_θW f U (homOfLE (inf_le_left f U i j)),
    homOfLE_θW f U (homOfLE (inf_le_right f U i j))]

variable (h : ∀ u : U.left, ∃ W : U.left.Opens, u ∈ W ∧ f.Etale.essImage (Etale.mk (W.ι ≫ U.hom)))

/-- The open cover of `U` by the indices. -/
noncomputable def cover : U.left.OpenCover :=
  Scheme.Cover.mkOfCovers (Idx f U) (fun W ↦ W.1.toScheme) (fun W ↦ W.1.ι) (fun u ↦ by
    obtain ⟨W, hu, hW⟩ := h u
    exact ⟨⟨W, hW⟩, ⟨u, hu⟩, rfl⟩)

/-- The comparison map `U ⟶ glued ×_Y X`, glued from the `θW`. -/
noncomputable def θ : U.left ⟶ pullback (glued f U).hom f :=
  (cover f U h).glueMorphisms (θW f U) (θW_compat f U)

lemma ι_θ (W : Idx f U) : W.1.ι ≫ θ f U h = θW f U W :=
  (cover f U h).ι_glueMorphisms (θW f U) (θW_compat f U) W

lemma θ_snd : θ f U h ≫ pullback.snd (glued f U).hom f = U.hom := by
  apply (cover f U h).hom_ext
  intro W
  change W.1.ι ≫ θ f U h ≫ _ = W.1.ι ≫ U.hom
  rw [← Category.assoc, ι_θ, θW, Category.assoc]
  have h1 : (f.Etale.map (ι f U W)).left ≫ pullback.snd (glued f U).hom f =
      pullback.snd (V f U W).hom f := MorphismProperty.Over.w (f.Etale.map (ι f U W))
  have h2 : (e f U W).inv.left ≫ pullback.snd (V f U W).hom f = W.1.ι ≫ U.hom :=
    MorphismProperty.Over.w (e f U W).inv
  rw [h1, h2]

lemma fst_θ_pt (W : Idx f U) (x : (V f U W).left) :
    pullback.fst (glued f U).hom f (θ f U h (pt f U W x)) = (ι f U W).left x := by
  obtain ⟨y, rfl⟩ := (homeo f U W).surjective x
  simp only [pt, Homeomorph.symm_apply_apply]
  have h1 : θ f U h (W.1.ι ((e f U W).hom.left y)) =
      (f.Etale.map (ι f U W)).left ((e f U W).inv.left ((e f U W).hom.left y)) := by
    change (W.1.ι ≫ θ f U h) _ = ((e f U W).inv.left ≫ (f.Etale.map (ι f U W)).left) _
    rw [ι_θ, θW]
    rfl
  have h2 : (e f U W).inv.left ((e f U W).hom.left y) = y := by
    change ((e f U W).hom.left ≫ (e f U W).inv.left) y = y
    rw [← MorphismProperty.Comma.comp_left, Iso.hom_inv_id]
    rfl
  rw [h1, h2, homeo_apply]
  change (_ ≫ pullback.fst _ f) y = (pullback.fst _ f ≫ _) y
  exact congrArg (fun φ ↦ φ y) (etale_map_left_comp_fst f (ι f U W))

lemma θ_injective : Function.Injective (θ f U h).base := by
  intro u u' huu'
  obtain ⟨W, hW⟩ := h u
  obtain ⟨W', hW'⟩ := h u'
  obtain ⟨x, hx⟩ : u ∈ Set.range (pt f U ⟨W, hW.2⟩) := by rw [range_pt]; exact hW.1
  obtain ⟨x', hx'⟩ : u' ∈ Set.range (pt f U ⟨W', hW'.2⟩) := by rw [range_pt]; exact hW'.1
  rw [← hx, ← hx'] at huu' ⊢
  have := congrArg (pullback.fst (glued f U).hom f) huu'
  rw [fst_θ_pt, fst_θ_pt, ι_left_eq_iff] at this
  obtain ⟨l, g, g', y, rfl, rfl⟩ := this
  rw [pt_map, pt_map]

lemma θ_surjective : Function.Surjective (θ f U h).base := by
  intro p
  obtain ⟨W, x, hx⟩ := exists_ι_left_eq f U (pullback.fst (glued f U).hom f p)
  refine ⟨pt f U W x, (pullback.fst (glued f U).hom f).injective ?_⟩
  rw [fst_θ_pt, hx]

instance : IsLocalIso (θ f U h) where
  exists_isOpenImmersion u := by
    obtain ⟨W, hu, hW⟩ := h u
    refine ⟨W, hu, ?_⟩
    rw [ι_θ f U h ⟨W, hW⟩]
    infer_instance

instance : IsOpenImmersion (θ f U h) :=
  IsOpenImmersion.of_isLocalIso_of_injective _ (θ_injective f U h)

instance : IsIso (θ f U h) :=
  isIso_of_isOpenImmersion_of_opensRange_eq_top _
    (by ext1; simpa using Set.range_eq_univ.mpr (θ_surjective f U h))

end Glue

end EtaleEssImageGluing

/-- **The essential image of base change along a universal homeomorphism is local**: an étale
`X`-scheme `U` is the base change of an étale `Y`-scheme as soon as every point of `U` has an
open neighbourhood which is. -/
theorem etale_essImage_of_forall_exists_mem (U : X.Etale)
    (h : ∀ u : U.left, ∃ W : U.left.Opens, u ∈ W ∧ f.Etale.essImage (Etale.mk (W.ι ≫ U.hom))) :
    f.Etale.essImage U :=
  ⟨EtaleEssImageGluing.glued f U, ⟨(MorphismProperty.Over.isoMk
    (asIso (EtaleEssImageGluing.θ f U h)) (EtaleEssImageGluing.θ_snd f U h)).symm⟩⟩

end Scheme.Hom

end AlgebraicGeometry
