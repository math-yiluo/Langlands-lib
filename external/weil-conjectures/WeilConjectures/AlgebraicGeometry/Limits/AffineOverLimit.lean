/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Integral.FiniteApproximation

/-!
# Cofiltered limits of schemes affine over a base

Let `S` be a scheme and `{Dᵢ}` a cofiltered diagram (indexed by a small category) of schemes
over `S` whose structure morphisms `pᵢ : Dᵢ ⟶ S` are affine. Then the limit `lim Dᵢ` exists in
the category of schemes (EGA IV 8.2.3, Stacks Project Tag 01YX): it is the relative spectrum over
`S` of the quasi-coherent `𝒪_S`-algebra `U ↦ colim Γ(Dᵢ, pᵢ⁻¹ U)`, and over an affine open
`U ⊆ S` it is `Spec (colim Γ(Dᵢ, pᵢ⁻¹ U))`.

We construct the quasi-coherent algebra as a filtered colimit of presheaves of rings on the small
affine Zariski site of `S`: the colimit of coequifibered (quasi-coherent) algebras is again
coequifibered (`CategoryTheory.NatTrans.coequifibered_comp_colimitι`, since pushouts commute
with colimits). Its relative spectrum
(`AlgebraicGeometry.Scheme.AffineZariskiSite.relativeGluingData`)
carries a cone over `D`, and this cone is a limit cone since it is so over the affine opens of
`S` (`AlgebraicGeometry.isLimitOfIsLimitOpensCone'`), where it is `Spec` of a colimit of rings.

## Main definitions and results

- `AlgebraicGeometry.Scheme.AffineOverLimit.limitCone`: the limit cone.
- `AlgebraicGeometry.Scheme.AffineOverLimit.isLimitLimitCone`: it is a limit cone.
- `AlgebraicGeometry.Scheme.hasLimit_of_isAffineHom`: cofiltered diagrams of schemes affine
  over a base have limits.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory.NatTrans

variable {J K C : Type*} [Category* J] [Category* K] [Category* C] {A : J ⥤ C}
  {G : K ⥤ J ⥤ C} [HasColimit G] [∀ j, PreservesColimit G ((evaluation J C).obj j)]

/-- **Colimits of coequifibered natural transformations.** Let `G` be a diagram of functors
`J ⥤ C` under a fixed functor `A`, via coequifibered natural transformations `α k : A ⟶ G k`
compatible with the transition maps. Then the induced natural transformation `A ⟶ colim G` is
coequifibered: pushout squares are stable under colimits (computed pointwise). -/
theorem coequifibered_of_forall_comp_colimitι (α : ∀ k, A ⟶ G.obj k)
    (hα : ∀ k, (α k).Coequifibered) (hcomp : ∀ {k k'} (f : k ⟶ k'), α k ≫ G.map f = α k')
    [Nonempty K] (β : A ⟶ colimit G) (hβ : ∀ k, α k ≫ colimit.ι G k = β) : β.Coequifibered := by
  intro U U' u
  have hc (V : J) : IsColimit (((evaluation J C).obj V).mapCocone (colimit.cocone G)) :=
    isColimitOfPreserves _ (colimit.isColimit G)
  have hβ' (k : K) (V : J) : (α k).app V ≫ (colimit.ι G k).app V = β.app V := by
    rw [← NatTrans.comp_app, hβ]
  have hw (k : K) (s : PushoutCocone (A.map u) (β.app U)) :
      A.map u ≫ s.inl = (α k).app U ≫ (colimit.ι G k).app U ≫ s.inr := by
    rw [s.condition, ← Category.assoc, hβ' k U]
  let h (s : PushoutCocone (A.map u) (β.app U)) (k : K) : (G.obj k).obj U' ⟶ s.pt :=
    (hα k u).desc s.inl ((colimit.ι G k).app U ≫ s.inr) (hw k s)
  have hnat (s : PushoutCocone (A.map u) (β.app U)) {k k' : K} (f : k ⟶ k') :
      (G.map f).app U' ≫ h s k' = h s k := by
    refine (hα k u).hom_ext ?_ ?_
    · rw [← Category.assoc, ← NatTrans.comp_app, hcomp, IsPushout.inl_desc, IsPushout.inl_desc]
    · rw [IsPushout.inr_desc, ← Category.assoc, NatTrans.naturality, Category.assoc,
        IsPushout.inr_desc, ← Category.assoc, ← NatTrans.comp_app, colimit.w]
  let c (s : PushoutCocone (A.map u) (β.app U)) : Cocone (G ⋙ (evaluation J C).obj U') :=
    { pt := s.pt
      ι := { app := h s, naturality := fun k k' f ↦ (hnat s f).trans (Category.comp_id _).symm } }
  refine IsPushout.of_isColimit' ⟨(β.naturality u)⟩
    (PushoutCocone.IsColimit.mk _ (fun s ↦ (hc U').desc (c s)) (fun s ↦ ?_) (fun s ↦ ?_)
      (fun s m h₁ h₂ ↦ ?_))
  · obtain ⟨k⟩ := ‹Nonempty K›
    rw [← hβ' k U', Category.assoc]
    exact (congrArg _ ((hc U').fac _ k)).trans (IsPushout.inl_desc _ _ _ _)
  · refine (hc U).hom_ext fun k ↦ ?_
    change (colimit.ι G k).app U ≫ _ ≫ _ = _
    rw [← Category.assoc, ← NatTrans.naturality, Category.assoc]
    exact (congrArg _ ((hc U').fac _ k)).trans (IsPushout.inr_desc _ _ _ _)
  · refine (hc U').hom_ext fun k ↦ ?_
    refine ((hc U').fac _ k).symm ▸ (hα k u).hom_ext ?_ ?_
    · change _ ≫ (colimit.ι G k).app U' ≫ m = _
      rw [IsPushout.inl_desc, ← Category.assoc, hβ' k U']
      exact h₁
    · change _ ≫ (colimit.ι G k).app U' ≫ m = _
      rw [IsPushout.inr_desc, ← Category.assoc, NatTrans.naturality, Category.assoc]
      exact congrArg _ h₂

end CategoryTheory.NatTrans

namespace AlgebraicGeometry.Scheme.AffineOverLimit

open AffineZariskiSite

variable {S : Scheme.{u}} {I : Type u} [SmallCategory I] (D : I ⥤ Scheme.{u})
  (p : ∀ i, D.obj i ⟶ S) (hp : ∀ {i j : I} (g : i ⟶ j), D.map g ≫ p j = p i)

include hp in
/-- The preimage of `pᵢ⁻¹ U` under a transition map is `pⱼ⁻¹ U`. -/
lemma preimage_map_preimage {i j : I} (g : j ⟶ i) (U : S.Opens) :
    D.map g ⁻¹ᵁ p i ⁻¹ᵁ U = p j ⁻¹ᵁ U := by
  rw [← Scheme.Hom.comp_preimage, hp]

/-- The presheaf of rings `U ↦ Γ(Dᵢ, pᵢ⁻¹ U)` on the affine opens of `S`, i.e. the direct image
of `𝒪_{Dᵢ}`. -/
noncomputable def sections (i : I) : S.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} where
  obj U := Γ(D.obj i, p i ⁻¹ᵁ U.unop.toOpens)
  map f := (D.obj i).presheaf.map (homOfLE ((p i).preimage_mono (toOpens_mono f.unop.le))).op
  map_id _ := (D.obj i).presheaf.map_id _
  map_comp _ _ := ((D.obj i).presheaf.map_comp _ _)

/-- The sections of `(pᵢ)_* 𝒪_{Dᵢ}` over `U` are `Γ(Dᵢ, pᵢ⁻¹ U)`. -/
lemma sections_obj (i : I) (U : S.AffineZariskiSiteᵒᵖ) :
    (sections D p i).obj U = Γ(D.obj i, p i ⁻¹ᵁ U.unop.toOpens) := rfl


/-- The structure morphism `𝒪_S ⟶ (pᵢ)_* 𝒪_{Dᵢ}`. -/
noncomputable def sectionsι (i : I) : (toOpensFunctor S).op ⋙ S.presheaf ⟶ sections D p i where
  app U := (p i).app U.unop.toOpens
  naturality _ _ _ := (p i).naturality _

/-- The structure morphism on sections is `pᵢ^*`. -/
lemma sectionsι_app (i : I) (U : S.AffineZariskiSiteᵒᵖ) :
    (sectionsι D p i).app U = (p i).app U.unop.toOpens := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The direct image of the structure sheaf along an affine morphism is quasi-coherent:
`Γ(Dᵢ, pᵢ⁻¹ D(r)) = Γ(Dᵢ, pᵢ⁻¹ U)[1/r]`. -/
lemma coequifibered_sectionsι [∀ i, IsAffineHom (p i)] (i : I) :
    (sectionsι D p i).Coequifibered := by
  refine coequifibered_iff_forall_isLocalizationAway.mpr fun U r ↦ ?_
  have hU : IsAffineOpen (p i ⁻¹ᵁ U.toOpens) := U.2.preimage (p i)
  have e : p i ⁻¹ᵁ (U.basicOpen r).toOpens = (D.obj i).basicOpen ((p i).app U.toOpens r) :=
    Scheme.preimage_basicOpen _ _
  change @IsLocalization.Away Γ(D.obj i, p i ⁻¹ᵁ U.toOpens) _ ((p i).app U.toOpens r)
    Γ(D.obj i, p i ⁻¹ᵁ (U.basicOpen r).toOpens) _
    ((D.obj i).presheaf.map
      (homOfLE ((p i).preimage_mono (toOpens_mono (U.basicOpen_le r)))).op).hom.toAlgebra
  rw! (castMode := .all) [e]
  exact hU.isLocalization_basicOpen _


/-- The map induced on sections by an endomorphism equal to the identity. -/
lemma appLE_eq_map_of_eq_id {X : Scheme.{u}} (g : X ⟶ X) (hg : g = 𝟙 X) (U V : X.Opens)
    (e : V ≤ g ⁻¹ᵁ U) : g.appLE U V e = X.presheaf.map (homOfLE (by subst hg; exact e)).op := by
  subst hg
  exact Category.id_comp _

include hp in
/-- The diagram `i ↦ (pᵢ)_* 𝒪_{Dᵢ}` of quasi-coherent `𝒪_S`-algebras. -/
@[simps]
noncomputable def diagram : Iᵒᵖ ⥤ S.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} where
  obj i := sections D p i.unop
  map {i j} φ :=
    { app U := (D.map φ.unop).appLE _ _ (preimage_map_preimage D p hp φ.unop U.unop.toOpens).ge
      naturality U V f := by
        simp only [sections, Scheme.Hom.map_appLE,
          Scheme.Hom.appLE_map] }
  map_id i := by
    ext U : 2
    exact (appLE_eq_map_of_eq_id _ (D.map_id i.unop) _ _ _).trans ((D.obj _).presheaf.map_id _)
  map_comp {i j k} φ ψ := by
    ext U : 2
    rw [NatTrans.comp_app, Scheme.Hom.appLE_comp_appLE]
    exact Scheme.Hom.appLE_congr_hom (D.map_comp ψ.unop φ.unop) _ _ _ _

include hp in
/-- The structure morphisms are compatible with the transition maps. -/
lemma sectionsι_comp_diagram_map {i j : Iᵒᵖ} (φ : i ⟶ j) :
    sectionsι D p i.unop ≫ (diagram D p hp).map φ = sectionsι D p j.unop := by
  ext U : 2
  rw [NatTrans.comp_app, sectionsι_app, sectionsι_app, diagram_map_app, Scheme.Hom.app_eq_appLE,
    Scheme.Hom.appLE_comp_appLE, Scheme.Hom.app_eq_appLE]
  exact Scheme.Hom.appLE_congr_hom (hp φ.unop) _ _ _ _


variable [IsCofiltered I] [∀ i, IsAffineHom (p i)]

attribute [local instance] IsFiltered.isConnected

/-- The quasi-coherent `𝒪_S`-algebra `U ↦ colim Γ(Dᵢ, pᵢ⁻¹ U)`. -/
noncomputable abbrev algebra : S.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} :=
  colimit (diagram D p hp)

/-- A chosen index. -/
noncomputable abbrev i₀ : I := (IsCofiltered.nonempty (C := I)).some

/-- The structure morphism `𝒪_S ⟶ colim (pᵢ)_* 𝒪_{Dᵢ}`. -/
noncomputable def algebraι : (toOpensFunctor S).op ⋙ S.presheaf ⟶ algebra D p hp :=
  sectionsι D p (i₀ (I := I)) ≫ colimit.ι (diagram D p hp) (.op (i₀ (I := I)))

omit [∀ i, IsAffineHom (p i)] in
/-- The structure morphism of the colimit factors through every stage. -/
lemma sectionsι_comp_colimitι (i : Iᵒᵖ) :
    sectionsι D p i.unop ≫ colimit.ι (diagram D p hp) i = algebraι D p hp :=
  constant_of_preserves_morphisms
    (fun i : Iᵒᵖ ↦ sectionsι D p i.unop ≫ colimit.ι (diagram D p hp) i)
    (fun _ _ φ ↦ by
      rw [← sectionsι_comp_diagram_map D p hp φ, Category.assoc, colimit.w]) i _

/-- The colimit `colim (pᵢ)_* 𝒪_{Dᵢ}` is a quasi-coherent `𝒪_S`-algebra. -/
lemma coequifibered_algebraι : (algebraι D p hp).Coequifibered :=
  NatTrans.coequifibered_of_forall_comp_colimitι (fun i ↦ sectionsι D p i.unop)
    (fun i ↦ coequifibered_sectionsι D p i.unop) (sectionsι_comp_diagram_map D p hp) _
    (sectionsι_comp_colimitι D p hp)

/-- The relative gluing datum of `Spec_S (colim (pᵢ)_* 𝒪_{Dᵢ})`. -/
noncomputable abbrev gluingData := relativeGluingData (coequifibered_algebraι D p hp)

/-- The limit `lim Dᵢ`, constructed as `Spec_S (colim (pᵢ)_* 𝒪_{Dᵢ})`. -/
noncomputable abbrev limitScheme : Scheme.{u} := (gluingData D p hp).glued

/-- The structure morphism `lim Dᵢ ⟶ S`. -/
noncomputable abbrev limitHom : limitScheme D p hp ⟶ S := (gluingData D p hp).toBase

/-- The transition maps of the relative gluing datum are `Spec` of restriction maps. -/
lemma gluingData_functor_map {U V : S.AffineZariskiSite} (f : U ⟶ V) :
    (gluingData D p hp).functor.map f = Spec.map ((algebra D p hp).map f.op) := rfl


/-- The chart `Spec Γ(Dᵢ, pᵢ⁻¹ U) ⟶ Dᵢ` over an affine open `U ⊆ S`. -/
noncomputable abbrev chart (i : I) (U : S.AffineZariskiSite) :
    Spec ((sections D p i).obj (.op U)) ⟶ D.obj i :=
  (U.2.preimage (p i)).fromSpec

omit [IsCofiltered I] in
/-- The chart over `U` lies over the chart `Spec Γ(S, U) ⟶ S`. -/
lemma chart_comp_p (i : I) (U : S.AffineZariskiSite) :
    chart D p i U ≫ p i = Spec.map ((sectionsι D p i).app (.op U)) ≫ U.2.fromSpec := by
  rw [sectionsι_app, Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec]

/-- The charts `Spec (colim Γ(Dⱼ, pⱼ⁻¹ U)) ⟶ Spec Γ(Dᵢ, pᵢ⁻¹ U) ⟶ Dᵢ` are compatible with the
restrictions along basic opens. -/
lemma specMap_ι_chart_naturality (i : I) {U V : S.AffineZariskiSite} (f : U ⟶ V) :
    Spec.map ((algebra D p hp).map f.op) ≫
        Spec.map ((colimit.ι (diagram D p hp) (.op i)).app (.op V)) ≫ chart D p i V =
      Spec.map ((colimit.ι (diagram D p hp) (.op i)).app (.op U)) ≫ chart D p i U := by
  rw [← Spec.map_comp_assoc, ← NatTrans.naturality, Spec.map_comp_assoc]
  congr 1
  exact IsAffineOpen.map_fromSpec _ _ _

/-- The charts of the stages are compatible with the structure morphisms. -/
lemma specMap_ι_chart_p (i : I) (U : S.AffineZariskiSite) :
    Spec.map ((colimit.ι (diagram D p hp) (.op i)).app (.op U)) ≫ chart D p i U ≫ p i =
      Spec.map ((algebraι D p hp).app (.op U)) ≫ U.2.fromSpec := by
  rw [chart_comp_p, ← Spec.map_comp_assoc, ← NatTrans.comp_app,
    sectionsι_comp_colimitι D p hp (.op i)]

/-- The charts of the stages are compatible with the transition maps. -/
lemma specMap_ι_chart_map {i j : I} (g : i ⟶ j) (U : S.AffineZariskiSite) :
    Spec.map ((colimit.ι (diagram D p hp) (.op i)).app (.op U)) ≫ chart D p i U ≫ D.map g =
      Spec.map ((colimit.ι (diagram D p hp) (.op j)).app (.op U)) ≫ chart D p j U := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec _ (U.2.preimage (p j)) _
    (preimage_map_preimage D p hp g U.toOpens).ge, ← Spec.map_comp_assoc]
  congr 2
  exact congrArg (fun φ ↦ φ.app (.op U)) (colimit.w (diagram D p hp) g.op)

/-- The projection `lim Dᵢ ⟶ Dᵢ`, glued from `Spec (colim Γ(Dⱼ, pⱼ⁻¹ U)) ⟶ Spec Γ(Dᵢ, pᵢ⁻¹ U)`. -/
noncomputable def π (i : I) : limitScheme D p hp ⟶ D.obj i :=
  colimit.desc (gluingData D p hp).functor
    { pt := D.obj i
      ι :=
        { app U := Spec.map ((colimit.ι (diagram D p hp) (.op i)).app (.op U)) ≫ chart D p i U
          naturality {_ _} f :=
            (specMap_ι_chart_naturality D p hp i f).trans (Category.comp_id _).symm } }

/-- The projection `lim Dᵢ ⟶ Dᵢ` on the chart over `U`. -/
@[reassoc]
lemma ι_π (i : I) (U : S.AffineZariskiSite) :
    colimit.ι (gluingData D p hp).functor U ≫ π D p hp i =
      Spec.map ((colimit.ι (diagram D p hp) (.op i)).app (.op U)) ≫ chart D p i U :=
  colimit.ι_desc _ _

/-- The projections `lim Dᵢ ⟶ Dᵢ` lie over `S`. -/
@[reassoc (attr := simp)]
lemma π_p (i : I) : π D p hp i ≫ p i = limitHom D p hp :=
  colimit.hom_ext fun U ↦ (ι_π_assoc D p hp i U _).trans
    ((specMap_ι_chart_p D p hp i U).trans (ι_toBase _ U).symm)

/-- The projections `lim Dᵢ ⟶ Dᵢ` are compatible with the transition maps. -/
@[reassoc (attr := simp)]
lemma π_map {i j : I} (g : i ⟶ j) : π D p hp i ≫ D.map g = π D p hp j :=
  colimit.hom_ext fun U ↦ (ι_π_assoc D p hp i U _).trans
    ((specMap_ι_chart_map D p hp g U).trans (ι_π D p hp j U).symm)

/-- The cone over `D` with point `lim Dᵢ`. -/
@[simps]
noncomputable def limitCone : Cone D where
  pt := limitScheme D p hp
  π :=
    { app := π D p hp
      naturality _ _ g := by simp }


section IsLimit

variable (U : S.AffineZariskiSite)

/-- The diagram of rings `i ↦ Γ(Dᵢ, pᵢ⁻¹ U)`, as a diagram in `CommRingCatᵒᵖ`. -/
noncomputable abbrev ringDiagram : I ⥤ CommRingCat.{u}ᵒᵖ :=
  (diagram D p hp ⋙ (CategoryTheory.evaluation _ _).obj (.op U)).rightOp

/-- `colim Γ(Dᵢ, pᵢ⁻¹ U)` as a cocone over the rings `Γ(Dᵢ, pᵢ⁻¹ U)` for `i` over `i₀`. -/
noncomputable def ringCocone (i₁ : I) : Cocone (Over.forget i₁ ⋙ ringDiagram D p hp U).leftOp :=
  (((CategoryTheory.evaluation _ _).obj (Opposite.op U)).mapCocone
    (colimit.cocone (diagram D p hp))).whisker
    (Over.forget i₁).op

omit [∀ i, IsAffineHom (p i)] in
/-- The components of `ringCocone` are the colimit inclusions. -/
lemma ringCocone_ι_app (i₁ : I) (j : (Over i₁)ᵒᵖ) :
    (ringCocone D p hp U i₁).ι.app j =
      (colimit.ι (diagram D p hp) (.op j.unop.left)).app (.op U) := rfl

/-- `colim Γ(Dᵢ, pᵢ⁻¹ U)` is the colimit of the rings `Γ(Dᵢ, pᵢ⁻¹ U)` for `i` over `i₀`. -/
noncomputable def isColimitRingCocone (i₁ : I) : IsColimit (ringCocone D p hp U i₁) :=
  (Functor.Final.isColimitWhiskerEquiv (Over.forget i₁).op _).symm
    (isColimitOfPreserves _ (colimit.isColimit _))

/-- The restriction of a stage over `U` is `Spec Γ(Dⱼ, pⱼ⁻¹ U)`. -/
noncomputable def opensIso (i₁ : I) (j : Over i₁) :
    (opensDiagram D i₁ (p i₁ ⁻¹ᵁ U.toOpens)).obj j ≅
      ((Over.forget i₁ ⋙ ringDiagram D p hp U) ⋙ Scheme.Spec).obj j :=
  IsOpenImmersion.isoOfRangeEq (Scheme.Opens.ι _) (chart D p j.left U)
    ((Scheme.Opens.range_ι _).trans (by
      rw [preimage_map_preimage D p hp]
      exact (IsAffineOpen.range_fromSpec _).symm))

omit [IsCofiltered I] in
/-- The identification `opensIso` is compatible with the inclusions into `Dⱼ`. -/
@[reassoc (attr := simp)]
lemma opensIso_hom_chart (i₁ : I) (j : Over i₁) :
    (opensIso D p hp U i₁ j).hom ≫ chart D p j.left U = Scheme.Opens.ι _ :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The restricted diagram of stages over `U` is the diagram `Spec Γ(Dⱼ, pⱼ⁻¹ U)`. -/
noncomputable def opensDiagramIso (i₁ : I) :
    opensDiagram D i₁ (p i₁ ⁻¹ᵁ U.toOpens) ≅
      (Over.forget i₁ ⋙ ringDiagram D p hp U) ⋙ Scheme.Spec :=
  NatIso.ofComponents (opensIso D p hp U i₁) fun {j j'} k ↦ by
    rw [← cancel_mono (chart D p j'.left U), Category.assoc, opensIso_hom_chart,
      opensDiagram_map_ι]
    change _ = _ ≫ Spec.map ((D.map k.left).appLE _ _ _) ≫ chart D p j'.left U
    rw [IsAffineOpen.SpecMap_appLE_fromSpec _ (U.2.preimage _) (U.2.preimage _),
      opensIso_hom_chart_assoc]

/-- The restriction of `lim Dᵢ` over `U` is `Spec (colim Γ(Dᵢ, pᵢ⁻¹ U))`. -/
noncomputable def coneOpensIso (i₁ : I) :
    (opensCone D (limitCone D p hp) i₁ (p i₁ ⁻¹ᵁ U.toOpens)).pt ≅
      Spec ((algebra D p hp).obj (.op U)) :=
  IsOpenImmersion.isoOfRangeEq (Scheme.Opens.ι _) (colimit.ι (gluingData D p hp).functor U)
    ((Scheme.Opens.range_ι _).trans (by
      rw [← Scheme.Hom.coe_opensRange, ← toBase_preimage]
      change SetLike.coe ((π D p hp i₁ ≫ p i₁) ⁻¹ᵁ U.toOpens) = _
      rw [π_p]))

/-- The identification `coneOpensIso` is compatible with the inclusions. -/
@[reassoc (attr := simp)]
lemma coneOpensIso_hom_ι (i₁ : I) :
    (coneOpensIso D p hp U i₁).hom ≫ colimit.ι (gluingData D p hp).functor U =
      Scheme.Opens.ι _ :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The restriction of `lim Dᵢ` over an affine open `U ⊆ S` is the limit of the restrictions of
the stages, being `Spec` of a colimit of rings. -/
noncomputable def isLimitOpensCone (i₁ : I) :
    IsLimit (opensCone D (limitCone D p hp) i₁ (p i₁ ⁻¹ᵁ U.toOpens)) := by
  have hS := isLimitOfPreserves Scheme.Spec
    (isLimitConeOfCoconeLeftOp _ (isColimitRingCocone D p hp U i₁))
  refine (IsLimit.postcomposeHomEquiv (opensDiagramIso D p hp U i₁) _)
    (hS.ofIsoLimit (Cone.ext (coneOpensIso D p hp U i₁).symm fun j ↦ ?_))
  rw [Iso.symm_hom, Iso.eq_inv_comp, ← cancel_mono (chart D p j.left U)]
  simp only [Functor.mapCone_π_app, coneOfCoconeLeftOp_π_app, Cone.postcompose_obj_π,
    NatTrans.comp_app, opensDiagramIso, NatIso.ofComponents_hom_app, Category.assoc,
    opensIso_hom_chart, opensCone_π_ι, limitCone_π_app]
  change _ ≫ Spec.map ((colimit.ι (diagram D p hp) (.op j.left)).app (.op U)) ≫ _ = _
  rw [← ι_π, coneOpensIso_hom_ι_assoc]

end IsLimit

/-- **`lim Dᵢ` is a limit** of the cofiltered diagram `D` of schemes affine over `S`. -/
noncomputable def isLimitLimitCone : IsLimit (limitCone D p hp) :=
  isLimitOfIsLimitOpensCone' D (limitCone D p hp) i₀
    (fun U : S.AffineZariskiSite ↦ p i₀ ⁻¹ᵁ U.toOpens) (by
      refine eq_top_iff.mpr fun x _ ↦ ?_
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (p i₀ x)) isOpen_univ
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hxV⟩)
    fun U ↦ isLimitOpensCone D p hp U _

end AlgebraicGeometry.Scheme.AffineOverLimit

namespace AlgebraicGeometry.Scheme

/-- **Cofiltered limits of schemes affine over a base exist** (EGA IV 8.2.3, Stacks Project
Tag 01YX): if `{Dᵢ}` is a cofiltered diagram of schemes with compatible affine morphisms
`pᵢ : Dᵢ ⟶ S`, then `lim Dᵢ` exists. -/
theorem hasLimit_of_isAffineHom {S : Scheme.{u}} {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (p : ∀ i, D.obj i ⟶ S)
    (hp : ∀ {i j : I} (g : i ⟶ j), D.map g ≫ p j = p i) [∀ i, IsAffineHom (p i)] :
    HasLimit D :=
  ⟨⟨⟨_, AffineOverLimit.isLimitLimitCone D p hp⟩⟩⟩

end AlgebraicGeometry.Scheme
