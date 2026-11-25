/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FormalFibreCohomology
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapZeroAugmentation

/-! # Restricted tensor units in degree zero

Source: Stacks Project, Cohomology, Remark Tag 01FB, equation-choice.
(blueprint: lem-weil-pbc-tensor-unit-open-degree-zero).
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives

set_option backward.isDefEq.respectTransparency false in
private theorem zero_augmentation_apply {X Y : Scheme.{u}} (h : X ⟶ Y)
    {G : Y.Modules} {F : X.Modules} (φ : G ⟶ (pushforward h).obj F)
    (s : G.presheaf.obj (op ⊤)) :
    moduleCohomologyFMap h φ 0
      (((RingedSpace.globalSectionsFunctor Y.toRingedSpace).toRightDerivedZero.app G).hom
        s) =
    ((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app F).hom
      ((φ.app ⊤) s) := by
  have hx := ModuleCohomologyFMapData.map_zero_augmentation
    (Classical.choice (moduleCohomologyFMapData_nonempty h G F φ))
  have hs := congrArg (fun k ↦ k s) hx
  simp only [CategoryTheory.comp_apply] at hs
  exact hs

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restricted_unit_sections {X P : Scheme.{u}} (h : P ⟶ X)
    (U : X.Opens) (F : X.Modules) (M : P.Modules)
    (η : F ⟶ (pushforward h).obj M)
    (ψ : (restrictFunctor U.ι).obj F ⟶
      (pushforward (h.resLE U (h ⁻¹ᵁ U) le_rfl)).obj
        ((restrictFunctor (h ⁻¹ᵁ U).ι).obj M))
    (sq : (restrictAdjunction U.ι).unit.app F ≫
        (pushforward U.ι).map ψ ≫
        (pushforwardComp (h.resLE U (h ⁻¹ᵁ U) le_rfl) U.ι).hom.app
          ((restrictFunctor (h ⁻¹ᵁ U).ι).obj M) ≫
        (pushforwardCongr (h.resLE_comp_ι le_rfl)).hom.app
          ((restrictFunctor (h ⁻¹ᵁ U).ι).obj M) =
      η ≫ (pushforward h).map ((restrictAdjunction (h ⁻¹ᵁ U).ι).unit.app M) ≫
        (pushforwardComp (h ⁻¹ᵁ U).ι h).hom.app
          ((restrictFunctor (h ⁻¹ᵁ U).ι).obj M))
    (hW : (⊤ : P.Opens) ≤ h ⁻¹ᵁ U) (t : F.presheaf.obj (op U)) :
    (ψ.app ⊤) ((F.restrictAppIso U.ι ⊤).inv
      (F.presheaf.map (eqToHom U.ι_image_top).op t)) =
    (((restrictAdjunction (h ⁻¹ᵁ U).ι).unit.app M).app ⊤)
      (M.presheaf.map (homOfLE hW).op ((η.app U) t)) := by
  have hu := congrArg (fun k ↦ k.app U) sq
  simp only [Hom.comp_app, pushforwardComp_hom_app_app,
    pushforwardCongr_hom_app_app, pushforward_map_app,
    Functor.comp_obj, pushforward_obj_obj] at hu
  erw [Category.id_comp, Category.comp_id] at hu
  let W := h ⁻¹ᵁ U
  let N := (restrictFunctor W.ι).obj M
  let j : (⊤ : U.toScheme.Opens) ⟶ U.ι ⁻¹ᵁ U :=
    eqToHom U.ι_preimage_self.symm
  let k : (⊤ : W.toScheme.Opens) ⟶ W.ι ⁻¹ᵁ W :=
    eqToHom W.ι_preimage_self.symm
  have hn := ψ.mapPresheaf.naturality j.op
  have hu2 := congrArg (fun l ↦ l ≫ N.presheaf.map k.op) hu
  simp only [restrictAdjunction_unit_app_app, Category.assoc] at hu2
  simp only [mapPresheaf_app] at hn
  erw [← Functor.map_comp] at hu2
  erw [← hn] at hu2
  dsimp only [N] at hu2
  simp only [restrict_map] at hu2
  erw [← Functor.map_comp_assoc, ← Functor.map_comp] at hu2
  have ht := congrArg (fun l ↦ l t) hu2
  simp only [AddCommGrpCat.comp_apply] at ht
  simp only [restrictAdjunction_unit_app_app]
  change (ψ.app ⊤) (F.presheaf.map (eqToHom U.ι_image_top).op t) = _
  conv_rhs => erw [← AddCommGrpCat.comp_apply, ← Functor.map_comp]
  exact ht

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The restricted tensor-unit square commutes on augmented sections when the
inverse-image open is the whole fibre product.
Source: Stacks Project, Cohomology, Remark Tag 01FB (remark-explain-arrow),
equation-choice, specialized to degree zero.
(blueprint: lem-weil-pbc-tensor-unit-open-degree-zero).

Proof: Apply the canonical degree-zero augmentation square for moduleCohomologyFMap
first to the restricted h-map D.psi and then to the restriction-adjunction unit on
the fibre product. Their inputs are the section t identified with a section of the
restricted module by restrictAppIso, and the restriction of its tensor-unit image
along hV. The two resulting sections of the restricted tensor pullback agree:
evaluate D.unit_square at U = f inverse V and at t. PushforwardComp and
pushforwardCongr identify these with the same section on W = h inverse U;
the restriction-adjunction unit acts by restriction, and restrictAppIso identifies
sections over top with sections over U (respectively W). Since hV says W is top,
restriction from top to W followed by restriction back to top is the identity.
Naturality of restriction with the tensor unit therefore gives precisely the two
sections in question. Apply their common augmentation to obtain the equality.
No flatness is used. The calculation also applies to empty fibre products, empty
opens and zero sections. -/
theorem tensorUnit_open_degree_zero {X S : Scheme.{u}} (f : X ⟶ S) (y : S) (n : ℕ)
    (F : X.Modules) (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (formalFibreι f y n)).obj F))
    (V : S.Opens) (D : FlatBaseChangeOpenChoices f (formalFibreBaseMap S y n) F I J V)
    (hV : (⊤ : (formalFibre f y n).Opens) ≤ (formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V))
    (t : F.presheaf.obj (op (f ⁻¹ᵁ V))) :
    moduleCohomologyFMap ((formalFibreι f y n).resLE (f ⁻¹ᵁ V)
      ((formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl) D.psi 0
        (((RingedSpace.globalSectionsFunctor
          (f ⁻¹ᵁ V).toScheme.toRingedSpace).toRightDerivedZero.app
            ((restrictFunctor (f ⁻¹ᵁ V).ι).obj F)).hom
            ((F.restrictAppIso (f ⁻¹ᵁ V).ι ⊤).inv
              (F.presheaf.map (eqToHom (f ⁻¹ᵁ V).ι_image_top).op t))) =
    moduleCohomologyFMap ((formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι
      ((restrictAdjunction ((formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι).unit.app
        ((tensorPullback (formalFibreι f y n)).obj F)) 0
          (((RingedSpace.globalSectionsFunctor
            (formalFibre f y n).toRingedSpace).toRightDerivedZero.app
              ((tensorPullback (formalFibreι f y n)).obj F)).hom
              (((tensorPullback (formalFibreι f y n)).obj F).presheaf.map
                (homOfLE hV).op
                  ((((Classical.choose (exists_tensorPullbackAdjunction
                    (formalFibreι f y n))).unit.app F).val.app (op (f ⁻¹ᵁ V))).hom t))) := by
  let h := formalFibreι f y n
  let U := f ⁻¹ᵁ V
  let W := h ⁻¹ᵁ U
  let M := (tensorPullback h).obj F
  let s := (F.restrictAppIso U.ι ⊤).inv
    (F.presheaf.map (eqToHom U.ι_image_top).op t)
  let z := M.presheaf.map (homOfLE hV).op
    ((((Classical.choose (exists_tensorPullbackAdjunction h)).unit.app F).val.app
      (op U)).hom t)
  have ha := zero_augmentation_apply (h.resLE U W le_rfl) D.psi s
  have hb := zero_augmentation_apply W.ι ((restrictAdjunction W.ι).unit.app M) z
  have hc := restricted_unit_sections h U F M
    ((Classical.choose (exists_tensorPullbackAdjunction h)).unit.app F)
    D.psi D.unit_square hV t
  have hd := congrArg (fun x ↦
    ((RingedSpace.globalSectionsFunctor W.toScheme.toRingedSpace).toRightDerivedZero.app
      ((restrictFunctor W.ι).obj M)).hom x) hc
  dsimp only [h, U, W, M, s, z] at ha hb hd
  exact ha.trans (hd.trans hb.symm)

end AlgebraicGeometry.Scheme.Modules
