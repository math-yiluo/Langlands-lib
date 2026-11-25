/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.EtaleVanishingLocus
public import WeilConjectures.AlgebraicGeometry.Sites.SectionContinuity
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Sections of étale sheaves over limits of étale schemes

Let `F` be an abelian étale sheaf on a scheme `X`.

For an étale morphism `t : T ⟶ X` the pullback `t^* F` is the restriction of `F` along the
functor `T_ét ⥤ X_ét` composing with `t`: the pullback of sections `pullSection t F` from an
étale `X`-scheme `V` to `V` itself, viewed as an étale `T`-scheme, is bijective
(`AlgebraicGeometry.Etale.bijective_pullSection_of_etale`).

Together with the continuity of sections at inverse limits
(`AlgebraicGeometry.Etale.unitComparison_app_isColimit_of_isLimit`), this shows that for a
cofiltered system `(Dⱼ)` of quasi-compact quasi-separated étale `X`-schemes with affine
transition maps and with a terminal index, the sections of `F` over the `Dⱼ` have as colimit the
sections of the pullback of `F` to the limit `D` of the system
(`AlgebraicGeometry.Etale.exists_pullSection_eq_of_isLimit`,
`AlgebraicGeometry.Etale.exists_map_eq_zero_of_pullSection_eq_zero_of_isLimit`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

section EtalePullback

variable {X T : Scheme.{u}} (t : T ⟶ X) (h : AlgebraicGeometry.Etale t)
  (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})

set_option backward.isDefEq.respectTransparency false in
/-- For an étale `t`, the identification `t^* F ≅ j_t^* F` of the pullback with the restriction
along `T_ét ⥤ X_ét` sends the pullback `φ^* g` of a section `g` of `F` over `U` along
`φ : V ⟶ U` to the restriction of `g` along `φ`, viewed as a morphism of étale `X`-schemes. -/
lemma upperStarIsoLocalizationRestriction_hom_app_pullSection {V : T.Etale} {U : X.Etale}
    (φ : V.left ⟶ U.left) (hφ : φ ≫ U.hom = V.hom ≫ t) (g : F.obj.obj (op U)) :
    ((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} t h).hom.app F).hom.app
        (op V) (pullSection t F φ hφ g) =
      F.obj.map (MorphismProperty.Over.homMk φ hφ :
        (MorphismProperty.Over.map ⊤ h).obj V ⟶ U).op g := by
  set e := Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} t h
  have h₁ := Adjunction.unit_leftAdjointUniq_hom_app
    (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} t)
    (Etale.localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} t h) F
  have h₂ := congrArg (fun α ↦ α.hom.app (op U) g) h₁
  have h₃ : (e.hom.app F).hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ t).obj U))
      (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} t).unit.app F).hom.app (op U) g) =
      F.obj.map ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ t h trivial).counit.app U).op g :=
    h₂
  rw [pullSection, NatTrans.naturality_apply, h₃]
  change F.obj.map _ (F.obj.map _ g) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  congr 3
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  simp [homToPullback]

include h in
/-- **Sections of the pullback along an étale morphism.** For an étale `t : T ⟶ X`, an étale
`T`-scheme `V`, an étale `X`-scheme `U` and an isomorphism `φ : V ⟶ U` over `X`, the pullback
of sections `pullSection t F φ : F(U) ⟶ (t^* F)(V)` is bijective. -/
lemma bijective_pullSection_of_etale {V : T.Etale} {U : X.Etale} (φ : V.left ⟶ U.left)
    [IsIso φ] (hφ : φ ≫ U.hom = V.hom ≫ t) :
    Function.Bijective (pullSection t F φ hφ) := by
  let ψ : (MorphismProperty.Over.map ⊤ h).obj V ⟶ U := MorphismProperty.Over.homMk φ hφ
  have : IsIso ψ := ⟨MorphismProperty.Over.homMk (inv φ)
      (by rw [IsIso.inv_comp_eq, hφ]; rfl),
    MorphismProperty.Over.Hom.ext (by simp [ψ]), MorphismProperty.Over.Hom.ext (by simp [ψ])⟩
  have h₁ : Function.Bijective (F.obj.map ψ.op) :=
    ConcreteCategory.bijective_of_isIso (F.obj.map ψ.op)
  have h₂ : Function.Bijective
      (((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} t h).hom.app F).hom.app
        (op V)) :=
    ConcreteCategory.bijective_of_isIso (((sheafSections _ _).obj (op V)).map
      ((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} t h).hom.app F))
  have h₃ : (((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} t h).hom.app
      F).hom.app (op V)) ∘ pullSection t F φ hφ = F.obj.map ψ.op :=
    funext fun g ↦ upperStarIsoLocalizationRestriction_hom_app_pullSection t h F φ hφ g
  rw [← h₂.of_comp_iff', h₃]
  exact h₁

end EtalePullback

section Limit

variable {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
  {J : Type u} [SmallCategory J] (U : J ⥤ X.Etale)
  (c : Cone (U ⋙ Scheme.Etale.forget X ⋙ CategoryTheory.Over.forget X))
  (j₀ : J) (hj₀ : IsTerminal j₀) (t : c.pt ⟶ X) (ht : t = c.π.app j₀ ≫ (U.obj j₀).hom)

include hj₀ ht in
/-- The legs of a cone over a system of étale `X`-schemes with a terminal index are morphisms
over `X`. -/
lemma π_app_comp_hom_of_isTerminal (j : J) :
    c.π.app j ≫ (U.obj j).hom = (Scheme.Etale.mk (𝟙 c.pt)).hom ≫ t := by
  have h₁ : c.π.app j ≫ (U.map (hj₀.from j)).left = c.π.app j₀ := c.w (hj₀.from j)
  have h₂ : (U.map (hj₀.from j)).left ≫ (U.obj j₀).hom = (U.obj j).hom :=
    MorphismProperty.Over.w _
  rw [ht, ← h₁, Category.assoc, h₂]
  exact (Category.id_comp _).symm

namespace SectionLimit

/-- The structure morphisms `Dⱼ ⟶ D_{j₀}` of a system of étale `X`-schemes to its terminal
index. -/
noncomputable def toTerminal :
    U ⋙ Scheme.Etale.forget X ⋙ CategoryTheory.Over.forget X ⟶
      (Functor.const J).obj (U.obj j₀).left where
  app j := (U.map (hj₀.from j)).left
  naturality j k g := by
    change (U.map g).left ≫ (U.map (hj₀.from k)).left = (U.map (hj₀.from j)).left ≫ 𝟙 _
    rw [Category.comp_id, ← etale_comp_left, ← U.map_comp, hj₀.hom_ext (g ≫ hj₀.from k)]

/-- The components of `toTerminal`. -/
lemma toTerminal_app (j : J) : (toTerminal U j₀ hj₀).app j = (U.map (hj₀.from j)).left := rfl


/-- The étale `D_{j₀}`-scheme `D_{j₀} ×_{D_{j₀}} Dⱼ`, isomorphic to `Dⱼ`. -/
noncomputable def auxObj (j : J) : (U.obj j₀).left.Etale :=
  (MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale
    (U.map (hj₀.from j)).left)).obj ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤
      (U.map (hj₀.from j)).left).obj (Scheme.Etale.mk (𝟙 (U.obj j₀).left)))

/-- The structure morphism of `auxObj`. -/
lemma auxObj_hom (j : J) : (auxObj U j₀ hj₀ j).hom =
    pullback.snd (Scheme.Etale.mk (𝟙 (U.obj j₀).left)).hom (U.map (hj₀.from j)).left ≫
      (U.map (hj₀.from j)).left :=
  rfl

/-- A section of `F` over `Dⱼ`, as a section of the pullback to `Dⱼ` of the pullback of `F` to
`D_{j₀}`, over `D_{j₀} ×_{D_{j₀}} Dⱼ`. -/
noncomputable def aux (j : J) (s : F.obj.obj (op (U.obj j))) :
    ((U.map (hj₀.from j)).left)^*[AddCommGrpCat.{u + 1}].obj
      (((U.obj j₀).hom)^*[AddCommGrpCat.{u + 1}].obj F) |>.obj.obj
        (op ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤
          (U.map (hj₀.from j)).left).obj (Scheme.Etale.mk (𝟙 (U.obj j₀).left)))) :=
  pullSection (U.map (hj₀.from j)).left _ (V := (MorphismProperty.Over.pullback
      @AlgebraicGeometry.Etale ⊤ (U.map (hj₀.from j)).left).obj
        (Scheme.Etale.mk (𝟙 (U.obj j₀).left))) (U := auxObj U j₀ hj₀ j) (𝟙 _)
    (Category.id_comp _)
    (pullSection (U.obj j₀).hom F (V := auxObj U j₀ hj₀ j) (U := U.obj j)
      (pullback.snd (Scheme.Etale.mk (𝟙 (U.obj j₀).left)).hom (U.map (hj₀.from j)).left)
      (by rw [auxObj_hom, Category.assoc, MorphismProperty.Over.w (U.map (hj₀.from j))]) s)

/-- `aux` sends zero to zero. -/
lemma aux_zero (j : J) : aux F U j₀ hj₀ j 0 = 0 := by
  rw [aux, pullSection_zero, pullSection_zero]

/-- `aux` is bijective: both pullbacks of sections in it are along étale morphisms and
isomorphisms. -/
lemma bijective_aux (j : J) : Function.Bijective (aux F U j₀ hj₀ j) := by
  have : IsIso (pullback.snd (Scheme.Etale.mk (𝟙 (U.obj j₀).left)).hom
      (U.map (hj₀.from j)).left) := inferInstanceAs (IsIso (pullback.snd (𝟙 _) _))
  exact (bijective_pullSection_of_etale _ inferInstance _ _ _).comp
    (bijective_pullSection_of_etale _ inferInstance _ _ _)

/-- The projection `D_{j₀} ×_{D_{j₀}} D ⟶ D` to the limit, as a morphism of étale
`D`-schemes. -/
noncomputable def limitProj :
    (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ (c.π.app j₀)).obj
      (Scheme.Etale.mk (𝟙 (U.obj j₀).left)) ⟶ Scheme.Etale.mk (𝟙 c.pt) :=
  MorphismProperty.Over.homMk (pullback.snd (Scheme.Etale.mk (𝟙 (U.obj j₀).left)).hom
    (c.π.app j₀)) (Category.comp_id _)

/-- The inverse of `limitProj`. -/
noncomputable def limitProjInv : Scheme.Etale.mk (𝟙 c.pt) ⟶
    (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ (c.π.app j₀)).obj
      (Scheme.Etale.mk (𝟙 (U.obj j₀).left)) :=
  MorphismProperty.Over.homMk (pullback.lift (c.π.app j₀) (𝟙 _)
    ((Category.comp_id _).trans (Category.id_comp _).symm))
    (pullback.lift_snd _ _ _)

/-- `limitProjInv` is a section of `limitProj`. -/
lemma limitProjInv_limitProj : limitProjInv U c j₀ ≫ limitProj U c j₀ = 𝟙 _ :=
  MorphismProperty.Over.Hom.ext (pullback.lift_snd _ _ _)

include ht in
/-- The image of `aux F U j₀ hj₀ j s` in the sections over the limit is the pullback of `s`. -/
lemma upperStarComp_inv_unitComparison_aux (j : J) (s : F.obj.obj (op (U.obj j))) :
    ((upperStarComp AddCommGrpCat.{u + 1} (c.π.app j₀) (U.obj j₀).hom t ht).inv.app F).hom.app
        (op ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ (c.π.app j₀)).obj
          (Scheme.Etale.mk (𝟙 (U.obj j₀).left))))
      ((unitComparison (c.π.app j) (U.map (hj₀.from j)).left (c.π.app j₀)
        (c.w (hj₀.from j)).symm (((U.obj j₀).hom)^*[AddCommGrpCat.{u + 1}].obj F)).hom.app
          (op (Scheme.Etale.mk (𝟙 (U.obj j₀).left))) (aux F U j₀ hj₀ j s)) =
      ((t)^*[AddCommGrpCat.{u + 1}].obj F).obj.map (limitProj U c j₀).op
        (pullSection t F (V := Scheme.Etale.mk (𝟙 c.pt)) (U := U.obj j) (c.π.app j)
          (π_app_comp_hom_of_isTerminal U c j₀ hj₀ t ht j) s) := by
  rw [unitComparison_hom_app_eq, aux]
  erw [restrictAlong_pullSection]
  rw [← restrictAlong_apply,
    restrictAlong_pullSection, map_pullSection]
  exact pullSection_congr _ _ _ (by simp [limitProj]) _

/-- The transition maps of the system of sections of the pullbacks of `F` are the restrictions
of sections of `F`. -/
lemma unitComparison_aux {j j' : J} (g : j' ⟶ j) (s : F.obj.obj (op (U.obj j))) :
    (unitComparison (U.map g).left (U.map (hj₀.from j)).left (U.map (hj₀.from j')).left
        (by rw [← etale_comp_left, ← U.map_comp, hj₀.hom_ext (g ≫ hj₀.from j)])
        (((U.obj j₀).hom)^*[AddCommGrpCat.{u + 1}].obj F)).hom.app
          (op (Scheme.Etale.mk (𝟙 (U.obj j₀).left))) (aux F U j₀ hj₀ j s) =
      aux F U j₀ hj₀ j' (F.obj.map (U.map g).op s) := by
  have hm : pullback.map (Scheme.Etale.mk (𝟙 (U.obj j₀).left)).hom (U.map (hj₀.from j')).left
      (Scheme.Etale.mk (𝟙 (U.obj j₀).left)).hom (U.map (hj₀.from j)).left (𝟙 _) (U.map g).left
      (𝟙 _) (by simp)
      (by rw [Category.comp_id, ← etale_comp_left, ← U.map_comp,
        hj₀.hom_ext (g ≫ hj₀.from j)]) ≫ (auxObj U j₀ hj₀ j).hom =
      (auxObj U j₀ hj₀ j').hom := by
    rw [auxObj_hom, auxObj_hom, pullback.lift_snd_assoc, Category.assoc, ← etale_comp_left,
      ← U.map_comp, hj₀.hom_ext (g ≫ hj₀.from j)]
  let κ : auxObj U j₀ hj₀ j' ⟶ auxObj U j₀ hj₀ j := MorphismProperty.Over.homMk _ hm
  have e₁ : pullSection (U.obj j₀).hom F (V := auxObj U j₀ hj₀ j') (U := U.obj j)
      (pullback.snd _ _ ≫ (U.map g).left)
      (by rw [auxObj_hom, Category.assoc, MorphismProperty.Over.w (U.map g), Category.assoc,
        MorphismProperty.Over.w (U.map (hj₀.from j'))]) s =
      (((U.obj j₀).hom)^*[AddCommGrpCat.{u + 1}].obj F).obj.map κ.op
        (pullSection (U.obj j₀).hom F (V := auxObj U j₀ hj₀ j) (U := U.obj j)
          (pullback.snd _ _)
          (by rw [auxObj_hom, Category.assoc, MorphismProperty.Over.w (U.map (hj₀.from j))])
          s) := by
    rw [map_pullSection]
    exact pullSection_congr _ _ _ (by simp [κ]) _
  rw [unitComparison_hom_app_eq, aux, aux]
  erw [restrictAlong_pullSection]
  rw [← pullSection_comp, e₁, ← pullSection_comp]
  exact pullSection_congr _ _ _ (by simp [κ]) _

end SectionLimit

open SectionLimit

variable [IsCofiltered J] [∀ j, CompactSpace (U.obj j).left]
  [∀ j, QuasiSeparatedSpace (U.obj j).left] [∀ {j k : J} (g : j ⟶ k), IsAffineHom (U.map g).left]

include ht in
/-- **Sections over a limit of étale schemes, surjectivity.** Let `(Dⱼ)` be a cofiltered system
of quasi-compact quasi-separated étale `X`-schemes with affine transition maps and a terminal
index, with limit `D`. Every section of the pullback of `F` to `D` is the pullback of a section
of `F` over some `Dⱼ`. -/
theorem exists_pullSection_eq_of_isLimit (hc : IsLimit c)
    (τ : ((t)^*[AddCommGrpCat.{u + 1}].obj F).obj.obj (op (Scheme.Etale.mk (𝟙 c.pt)))) :
    ∃ (j : J) (s : F.obj.obj (op (U.obj j))),
      pullSection t F (V := Scheme.Etale.mk (𝟙 c.pt)) (U := U.obj j) (c.π.app j)
        (π_app_comp_hom_of_isTerminal U c j₀ hj₀ t ht j) s = τ := by
  let W := Scheme.Etale.mk (𝟙 (U.obj j₀).left)
  let χ := ((upperStarComp AddCommGrpCat.{u + 1} (c.π.app j₀) (U.obj j₀).hom t ht).inv.app
    F).hom.app (op ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ (c.π.app j₀)).obj W))
  have hχ : Function.Bijective χ := ConcreteCategory.bijective_of_isIso
    (((sheafSections _ _).obj _).map
      ((upperStarComp AddCommGrpCat.{u + 1} (c.π.app j₀) (U.obj j₀).hom t ht).inv.app F))
  obtain ⟨σ, hσ⟩ := hχ.2 (((t)^*[AddCommGrpCat.{u + 1}].obj F).obj.map (limitProj U c j₀).op τ)
  have (j : J) : CompactSpace ((U ⋙ Scheme.Etale.forget X ⋙ CategoryTheory.Over.forget X).obj j) :=
    inferInstanceAs (CompactSpace (U.obj j).left)
  have (j : J) : QuasiSeparatedSpace
      ((U ⋙ Scheme.Etale.forget X ⋙ CategoryTheory.Over.forget X).obj j) :=
    inferInstanceAs (QuasiSeparatedSpace (U.obj j).left)
  have {j k : J} (g : j ⟶ k) :
      IsAffineHom ((U ⋙ Scheme.Etale.forget X ⋙ CategoryTheory.Over.forget X).map g) :=
    inferInstanceAs (IsAffineHom (U.map g).left)
  have : CompactSpace W.left := inferInstanceAs (CompactSpace (U.obj j₀).left)
  have : QuasiSeparatedSpace W.left := inferInstanceAs (QuasiSeparatedSpace (U.obj j₀).left)
  obtain ⟨j, x, hx⟩ := unitComparison_app_surjective_of_isLimit _ (toTerminal U j₀ hj₀) c
    (c.π.app j₀) (fun j ↦ (c.w (hj₀.from j)).symm) hc
    (((U.obj j₀).hom)^*[AddCommGrpCat.{u + 1}].obj F) W σ
  obtain ⟨s, rfl⟩ := (bijective_aux F U j₀ hj₀ j).2 x
  refine ⟨j, s, ?_⟩
  have hx' : (unitComparison (c.π.app j) (U.map (hj₀.from j)).left (c.π.app j₀)
      (c.w (hj₀.from j)).symm (((U.obj j₀).hom)^*[AddCommGrpCat.{u + 1}].obj F)).hom.app
        (op W) (aux F U j₀ hj₀ j s) = σ := hx
  have e := upperStarComp_inv_unitComparison_aux F U c j₀ hj₀ t ht j s
  rw [hx'] at e
  have e' := congrArg (((t)^*[AddCommGrpCat.{u + 1}].obj F).obj.map (limitProjInv U c j₀).op)
    (hσ.symm.trans e)
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp] at e'
  erw [limitProjInv_limitProj] at e'
  simp only [op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] at e'
  exact e'.symm

include ht in
/-- **Sections over a limit of étale schemes, injectivity.** In the situation of
`AlgebraicGeometry.Etale.exists_pullSection_eq_of_isLimit`, a section of `F` over `Dⱼ` whose
pullback to `D` vanishes already vanishes over some `D_{j'}`, `j' ⟶ j`. -/
theorem exists_map_eq_zero_of_pullSection_eq_zero_of_isLimit (hc : IsLimit c) (j : J)
    (s : F.obj.obj (op (U.obj j)))
    (hs : pullSection t F (V := Scheme.Etale.mk (𝟙 c.pt)) (U := U.obj j) (c.π.app j)
      (π_app_comp_hom_of_isTerminal U c j₀ hj₀ t ht j) s = 0) :
    ∃ (j' : J) (g : j' ⟶ j), F.obj.map (U.map g).op s = 0 := by
  let W := Scheme.Etale.mk (𝟙 (U.obj j₀).left)
  let χ := ((upperStarComp AddCommGrpCat.{u + 1} (c.π.app j₀) (U.obj j₀).hom t ht).inv.app
    F).hom.app (op ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ (c.π.app j₀)).obj W))
  have hχ : Function.Bijective χ := ConcreteCategory.bijective_of_isIso
    (((sheafSections _ _).obj _).map
      ((upperStarComp AddCommGrpCat.{u + 1} (c.π.app j₀) (U.obj j₀).hom t ht).inv.app F))
  have (j : J) : CompactSpace ((U ⋙ Scheme.Etale.forget X ⋙ CategoryTheory.Over.forget X).obj j) :=
    inferInstanceAs (CompactSpace (U.obj j).left)
  have (j : J) : QuasiSeparatedSpace
      ((U ⋙ Scheme.Etale.forget X ⋙ CategoryTheory.Over.forget X).obj j) :=
    inferInstanceAs (QuasiSeparatedSpace (U.obj j).left)
  have {j k : J} (g : j ⟶ k) :
      IsAffineHom ((U ⋙ Scheme.Etale.forget X ⋙ CategoryTheory.Over.forget X).map g) :=
    inferInstanceAs (IsAffineHom (U.map g).left)
  have : CompactSpace W.left := inferInstanceAs (CompactSpace (U.obj j₀).left)
  have : QuasiSeparatedSpace W.left := inferInstanceAs (QuasiSeparatedSpace (U.obj j₀).left)
  have h₁ := upperStarComp_inv_unitComparison_aux F U c j₀ hj₀ t ht j s
  rw [hs, map_zero] at h₁
  have h₂ : (unitComparison (c.π.app j) ((toTerminal U j₀ hj₀).app j) (c.π.app j₀)
      (c.w (hj₀.from j)).symm (((U.obj j₀).hom)^*[AddCommGrpCat.{u + 1}].obj F)).hom.app
        (op W) (aux F U j₀ hj₀ j s) = 0 :=
    hχ.1 (h₁.trans (map_zero _).symm)
  obtain ⟨j', g, hg⟩ := exists_unitComparison_app_eq_zero_of_isLimit _ (toTerminal U j₀ hj₀) c
    (c.π.app j₀) (fun j ↦ (c.w (hj₀.from j)).symm) hc
    (((U.obj j₀).hom)^*[AddCommGrpCat.{u + 1}].obj F) W j _ h₂
  refine ⟨j', g, (bijective_aux F U j₀ hj₀ j').1 ?_⟩
  rw [← unitComparison_aux, aux_zero]
  exact hg

end Limit

end AlgebraicGeometry.Etale
