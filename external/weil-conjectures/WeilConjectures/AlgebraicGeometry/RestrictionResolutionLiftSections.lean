/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-! # Sections of a restriction-adjunction lift

Source: Stacks Project, Cohomology, Tags 01FB and 01E4.
(blueprint: lem-weil-restriction-resolution-lift-sections).
-/

@[expose] public section
universe uBC
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] AlgebraicGeometry.Scheme.Modules.enoughInjectives

private lemma restrict_map_app {X Y : Scheme.{uBC}} (f : X ⟶ Y)
    [IsOpenImmersion f] {M N : Y.Modules} (v : M ⟶ N) (V : X.Opens) :
    Hom.app ((restrictFunctor f).map v) V = Hom.app v (f ''ᵁ V) := rfl

@[reassoc]
private lemma app_naturality {X : Scheme.{uBC}} {M N : X.Modules}
    (v : M ⟶ N) {V T : X.Opens} (i : T ⟶ V) :
    Hom.app v V ≫ N.presheaf.map i.op = M.presheaf.map i.op ≫ Hom.app v T :=
  (v.mapPresheaf.naturality i.op).symm

@[reassoc]
private lemma comparison_sections_comp {X Y : Scheme.{uBC}} (j : Y ⟶ X)
    [IsOpenImmersion j] {F : X.Modules} {K : Y.Modules} (e : K ≅ F.restrict j)
    {V Q : X.Opens} {T₀ T₁ T₂ T₃ : Y.Opens}
    (i₁ : j ''ᵁ T₀ ⟶ V) (i₂ : T₁ ⟶ T₀) (i₃ : T₂ ⟶ T₁) (i₄ : T₃ ⟶ T₂)
    (i₅ : Q ⟶ j ''ᵁ T₃) :
    F.presheaf.map i₁.op ≫ (F.restrict j).presheaf.map i₂.op ≫
      Hom.app e.inv T₁ ≫ K.presheaf.map i₃.op ≫ K.presheaf.map i₄.op ≫
        Hom.app e.hom T₃ ≫ F.presheaf.map i₅.op =
    F.presheaf.map (i₅ ≫ j.opensFunctor.map i₄ ≫ j.opensFunctor.map i₃ ≫
      j.opensFunctor.map i₂ ≫ i₁).op := by
  rw [app_naturality_assoc e.inv, app_naturality_assoc e.inv]
  have he : Hom.app e.inv T₃ ≫ Hom.app e.hom T₃ = 𝟙 _ := by
    rw [← Hom.comp_app, e.inv_hom_id, Hom.id_app]
  rw [← Category.assoc (Hom.app e.inv T₃), he, Category.id_comp]
  simp only [restrict_map, ← Functor.map_comp_assoc, ← Functor.map_comp]
  congr 1

-- Expanding the scheme restriction comparisons requires extra elaboration fuel.
private lemma raw_lift_sections {X Y : Scheme.{uBC}} (p : Y ⟶ X)
    {M : X.Modules} {N : Y.Modules} (φ : M ⟶ (pushforward p).obj N) (U : X.Opens)
    {D : U.toScheme.Modules} {K : (p ⁻¹ᵁ U).toScheme.Modules}
    (v : D ⟶ M.restrict U.ι) (e : K ≅ N.restrict (p ⁻¹ᵁ U).ι) :
    let W := p ⁻¹ᵁ U
    let h := p.resLE U W le_rfl
    let w := (restrictAdjunction W.ι).unit.app N
    let b : M ⟶ (pushforward U.ι).obj ((pushforward h).obj K) :=
      φ ≫ (pushforward p).map w ≫
        (pushforwardComp W.ι p).hom.app (N.restrict W.ι) ≫
        (pushforwardCongr (p.resLE_comp_ι (U := U) (V := W) le_rfl)).inv.app
          (N.restrict W.ι) ≫
        (pushforwardComp h U.ι).inv.app (N.restrict W.ι) ≫
        (pushforward U.ι).map ((pushforward h).map e.inv)
    let k := v ≫ ((restrictAdjunction U.ι).homEquiv M ((pushforward h).obj K)).symm b
    Hom.app k ⊤ ≫ K.presheaf.map
        (eqToHom (by simp) : (⊤ : W.toScheme.Opens) ⟶ h ⁻¹ᵁ ⊤).op ≫
      Hom.app e.hom ⊤ ≫ (restrictAppIso W.ι N ⊤).hom ≫
        N.presheaf.map (eqToHom W.ι_image_top.symm).op =
    Hom.app v ⊤ ≫ (restrictAppIso U.ι M ⊤).hom ≫
      M.presheaf.map (eqToHom U.ι_image_top.symm).op ≫ Hom.app φ U := by
  intro W h w b k
  simp only [k, Adjunction.homEquiv_counit, Hom.comp_app,
    restrict_map_app, restrictAdjunction_counit_app_app]
  simp only [b, w, Hom.comp_app, pushforward_map_app,
    pushforwardComp_hom_app_app, pushforwardComp_inv_app_app,
    pushforwardCongr_inv_app_app, restrictAdjunction_unit_app_app,
    restrictAppIso, Iso.refl_hom, Category.assoc]
  simp only [Category.id_comp]
  simp only [pushforward_obj_presheaf_map]
  let V := U.ι ''ᵁ (⊤ : U.toScheme.Opens)
  let T₀ := W.ι ⁻¹ᵁ (p ⁻¹ᵁ V)
  let T₁ := h ⁻¹ᵁ (U.ι ⁻¹ᵁ V)
  let T₂ := h ⁻¹ᵁ (⊤ : U.toScheme.Opens)
  let i₁ : W.ι ''ᵁ T₀ ⟶ p ⁻¹ᵁ V := homOfLE (W.ι.image_preimage_le _)
  let i₂ : T₁ ⟶ T₀ := eqToHom (by
    simpa only [Scheme.Hom.comp_preimage] using
      congrArg (fun f ↦ f ⁻¹ᵁ V) (p.resLE_comp_ι (U := U) (V := W) le_rfl))
  let i₃ : T₂ ⟶ T₁ := (TopologicalSpace.Opens.map h.base).map
    (eqToHom (U.ι.preimage_image_eq ⊤).symm)
  let i₄ : (⊤ : W.toScheme.Opens) ⟶ T₂ := eqToHom (by simp [T₂])
  let i₅ : W ⟶ W.ι ''ᵁ (⊤ : W.toScheme.Opens) := eqToHom W.ι_image_top.symm
  change Hom.app v ⊤ ≫ Hom.app φ V ≫ N.presheaf.map i₁.op ≫
    (N.restrict W.ι).presheaf.map i₂.op ≫ Hom.app e.inv T₁ ≫
      K.presheaf.map i₃.op ≫ K.presheaf.map i₄.op ≫
        Hom.app e.hom ⊤ ≫ N.presheaf.map i₅.op =
    Hom.app v ⊤ ≫ M.presheaf.map (eqToHom U.ι_image_top.symm).op ≫ Hom.app φ U
  calc
    _ = Hom.app v ⊤ ≫ Hom.app φ V ≫ N.presheaf.map
        (i₅ ≫ W.ι.opensFunctor.map i₄ ≫ W.ι.opensFunctor.map i₃ ≫
          W.ι.opensFunctor.map i₂ ≫ i₁).op :=
      congrArg (fun z ↦ Hom.app v ⊤ ≫ Hom.app φ V ≫ z)
        (comparison_sections_comp W.ι e i₁ i₂ i₃ i₄ i₅)
    _ = Hom.app v ⊤ ≫ Hom.app φ V ≫
        ((pushforward p).obj N).presheaf.map (eqToHom U.ι_image_top.symm).op := by
      rw [pushforward_obj_presheaf_map]
      exact congrArg (fun z ↦ Hom.app v ⊤ ≫ Hom.app φ V ≫ N.presheaf.map z)
        (Subsingleton.elim _ _)
    _ = _ := congrArg (fun z ↦ Hom.app v ⊤ ≫ z)
      (app_naturality φ (eqToHom U.ι_image_top.symm))

-- The nested complex functors and their restriction adjunction need extra elaboration fuel.
/-- Evaluate a restriction-adjunction lift on sections, with arbitrary resolutions
and their prescribed restriction comparisons. This calculation involves one scheme
map only, and no base-change square or equality between composite inverse images.
Source: Stacks Project, Tags 01FB and 01E4, the resolution and open-section
calculation; Mathlib AlgebraicGeometry.Modules.Sheaf, restriction unit/counit.
(blueprint: lem-weil-restriction-resolution-lift-sections).
Proof: Work in each degree. Expand the adjoint as restriction of b followed by
its counit. The counit is restriction along the equality U.ι⁻¹(U.ι(top))=top.
The unit on J restricts from p⁻¹(U.ι(top)) to W.ι(W.ι⁻¹(p⁻¹(U.ι(top)))).
The two pushforward composition comparisons are identity on sections and the
congruence comparison restricts along the equality p ∘ W.ι = U.ι ∘ h.
Use naturality to move the inverse target comparison past the counit and the
specified a.inv restriction. Use B.components to expand the final section
comparison and cancel B.comparison.inv against B.comparison.hom. Compose all
remaining restrictions by presheaf functoriality. The resulting restriction
is the equality W.ι(top)=W. Expand A.components and use naturality of t to
obtain A.sections.hom followed by evaluation of t on U. The calculation uses
neither injectivity nor the augmentations. For U empty all section groups are
zero; for p an identity it is the cancellation of the restriction comparisons. -/
theorem restrictionResolutionLift_sections {X Y : Scheme.{uBC}}
    (p : Y ⟶ X) {M : X.Modules} {N : Y.Modules}
    (I : InjectiveResolution M) (J : InjectiveResolution N)
    (t : I.cocomplex ⟶ ((pushforward p).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J.cocomplex)
    (U : X.Opens) (A : RestrictedResolutionSections I U)
    (B : RestrictedResolutionSections J (p ⁻¹ᵁ U)) :
  let W := p ⁻¹ᵁ U
  letI : (restrictFunctor U.ι).Additive :=
    (restrictAdjunction U.ι).left_adjoint_additive
  let h := p.resLE U W le_rfl
  let C := B.resolution.cocomplex
  let P := (pushforward U.ι).mapHomologicalComplex (ComplexShape.up ℕ)
  let H := (pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)
  let G := (pushforward p).mapHomologicalComplex (ComplexShape.up ℕ)
  let e₁ := NatIso.mapHomologicalComplex (pushforwardComp W.ι p)
    (ComplexShape.up ℕ)
  let e₂ := NatIso.mapHomologicalComplex
    (pushforwardCongr (p.resLE_comp_ι (U := U) (V := W) le_rfl))
    (ComplexShape.up ℕ)
  let e₃ := NatIso.mapHomologicalComplex (pushforwardComp h U.ι) (ComplexShape.up ℕ)
  let w := ((restrictAdjunction W.ι).unit.mapHomologicalComplex
    (ComplexShape.up ℕ)).app J.cocomplex
  let b : I.cocomplex ⟶ P.obj (H.obj C) :=
    t ≫ G.map w ≫ e₁.hom.app (((restrictFunctor W.ι).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J.cocomplex) ≫
      e₂.inv.app (((restrictFunctor W.ι).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj J.cocomplex) ≫
      e₃.inv.app (((restrictFunctor W.ι).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj J.cocomplex) ≫
      P.map (H.map B.comparison.inv)
  let k := A.comparison.hom ≫
    (((restrictAdjunction U.ι).mapHomologicalComplex (ComplexShape.up ℕ)).homEquiv
      I.cocomplex (H.obj C)).symm b
  let ΓS := (RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace ⋙
    forget₂ _ AddCommGrpCat.{uBC}).mapHomologicalComplex (ComplexShape.up ℕ)
  let ΓT := (RingedSpace.globalSectionsFunctor (p ⁻¹ᵁ U).toScheme.toRingedSpace ⋙
    forget₂ _ AddCommGrpCat.{uBC}).mapHomologicalComplex (ComplexShape.up ℕ)
  ∀ (a : ΓT.obj B.resolution.cocomplex ≅ ΓS.obj (H.obj B.resolution.cocomplex)),
    (∀ n : ℕ, a.inv.f n = (B.resolution.cocomplex.X n).presheaf.map
      (eqToHom (by simp) : (⊤ : (p ⁻¹ᵁ U).toScheme.Opens) ⟶
        h ⁻¹ᵁ (⊤ : U.toScheme.Opens)).op) →
    ΓS.map k ≫ a.inv ≫ B.sections.hom =
      A.sections.hom ≫
        ((RingedSpace.openModuleSections X.toRingedSpace U).mapHomologicalComplex
          (ComplexShape.up ℕ)).map t  := by
  intro W h C P H G e₁ e₂ e₃ w b k ΓS ΓT a ha
  apply HomologicalComplex.hom_ext
  intro n
  change Hom.app (k.f n) ⊤ ≫ a.inv.f n ≫ B.sections.hom.f n =
    A.sections.hom.f n ≫ Hom.app (t.f n) U
  rw [ha n, A.components n, B.components n]
  exact raw_lift_sections p (t.f n) U (A.comparison.hom.f n)
    ((HomologicalComplex.eval _ _ n).mapIso B.comparison)

end AlgebraicGeometry.Scheme.Modules
