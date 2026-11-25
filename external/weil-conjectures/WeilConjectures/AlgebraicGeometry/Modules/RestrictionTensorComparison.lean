/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal

/-!
# Restriction and tensor products of modules

## References

* Stacks Project, Modules, Lemma 01CD
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private theorem tensor_hom_ext {X : Scheme.{u}} {F G H : X.Modules}
    {a b : F ⊗ G ⟶ H}
    (h : ∀ (U : X.Opens) (s : Γ(F, U)) (t : Γ(G, U)),
      a.app U (tmulSection s t) = b.app U (tmulSection s t)) : a = b := by
  let β := fun U : X.Opensᵒᵖ ↦
    LinearMap.mk₂ Γ(X, U.unop) (fun s t ↦ a.app U.unop (tmulSection s t))
      (by intros; rw [add_tmulSection, map_add])
      (by intros; rw [smul_tmulSection, Hom.app_smul])
      (by intros; rw [tmulSection_add, map_add])
      (by intros; rw [tmulSection_smul, Hom.app_smul])
  have hβ : ∀ {U V : X.Opensᵒᵖ} (i : U ⟶ V) (s : Γ(F, U.unop))
      (t : Γ(G, U.unop)),
      β V (F.val.map i s) (G.val.map i t) = H.val.map i (β U s t) := by
    intro U V i s t
    change a.app V.unop (tmulSection (F.presheaf.map i s) (G.presheaf.map i t)) = _
    have hi := tmulSection_map (M := F) (N := G) (leOfHom i.unop) s t
    simp only [homOfLE_leOfHom] at hi
    exact (congrArg (a.app V.unop) hi.symm).trans
      (Hom.app_presheaf_map a i.unop _)
  obtain ⟨φ, hφ, huniq⟩ := SheafOfModules.tensor_bilinear_universal
    X.sheaf F G H β hβ
  exact (huniq a (by intro U s t; rfl)).trans (huniq b (by
    intro U s t
    exact (h U.unop s t).symm)).symm

set_option backward.isDefEq.respectTransparency false in
private noncomputable def restrictionPairing {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (F G : X.Modules) (V : Y.Opens) :
    Γ(F.restrict j, V) →ₗ[Γ(Y, V)] Γ(G.restrict j, V) →ₗ[Γ(Y, V)]
      Γ((F ⊗ G).restrict j, V) :=
  LinearMap.mk₂ Γ(Y, V)
    (fun s t ↦ tmulSection (M := F) (N := G) (U := j ''ᵁ V) s t)
    (by intros; exact add_tmulSection _ _ _)
    (by
      intro r s t
      change tmulSection (M := F) (N := G) (U := j ''ᵁ V)
        ((j.appIso V).inv r • (show Γ(F, j ''ᵁ V) from s)) t =
        (j.appIso V).inv r • tmulSection (M := F) (N := G) s t
      exact smul_tmulSection _ _ _)
    (by intros; exact tmulSection_add _ _ _)
    (by
      intro r s t
      change tmulSection (M := F) (N := G) (U := j ''ᵁ V)
        s ((j.appIso V).inv r • (show Γ(G, j ''ᵁ V) from t)) =
        (j.appIso V).inv r • tmulSection (M := F) (N := G) s t
      exact tmulSection_smul _ _ _)

set_option backward.isDefEq.respectTransparency false in
private theorem restrictionPairing_natural {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (F G : X.Modules) {U V : Y.Opensᵒᵖ} (i : U ⟶ V)
    (s : Γ(F.restrict j, U.unop)) (t : Γ(G.restrict j, U.unop)) :
    restrictionPairing j F G V.unop ((F.restrict j).val.map i s)
        ((G.restrict j).val.map i t) =
      ((F ⊗ G).restrict j).val.map i (restrictionPairing j F G U.unop s t) := by
  exact (tmulSection_map (leOfHom (j.opensFunctor.map i.unop)) s t).symm

set_option backward.isDefEq.respectTransparency false in
private theorem exists_restrictionTensorHom {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (F G : X.Modules) :
    ∃ c : F.restrict j ⊗ G.restrict j ⟶ (F ⊗ G).restrict j,
      ∀ (V : Y.Opens) (s : Γ(F.restrict j, V)) (t : Γ(G.restrict j, V)),
        c.app V (tmulSection s t) = restrictionPairing j F G V s t := by
  obtain ⟨c, hc, _⟩ := SheafOfModules.tensor_bilinear_universal Y.sheaf
    (F.restrict j) (G.restrict j) ((F ⊗ G).restrict j)
    (fun U ↦ restrictionPairing j F G U.unop) (restrictionPairing_natural j F G)
  exact ⟨c, fun V s t ↦ hc (Opposite.op V) s t⟩

set_option backward.isDefEq.respectTransparency false in
private noncomputable def inversePairing {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (F G : X.Modules) (U : X.Opens) :
    Γ(F, U) →ₗ[Γ(X, U)] Γ(G, U) →ₗ[Γ(X, U)]
      Γ((pushforward j).obj (F.restrict j ⊗ G.restrict j), U) :=
  LinearMap.mk₂ Γ(X, U)
    (fun s t ↦ tmulSection (M := F.restrict j) (N := G.restrict j) (U := j ⁻¹ᵁ U)
      (((restrictAdjunction j).unit.app F).app U s)
      (((restrictAdjunction j).unit.app G).app U t))
    (by intros; rw [map_add, add_tmulSection])
    (by
      intro r s t
      rw [Hom.app_smul]
      change tmulSection (M := F.restrict j) (N := G.restrict j)
        (j.app U r • (show Γ(F.restrict j, j ⁻¹ᵁ U) from
          ((restrictAdjunction j).unit.app F).app U s)) _ =
        j.app U r • tmulSection (M := F.restrict j) (N := G.restrict j) _ _
      exact smul_tmulSection _ _ _)
    (by intros; rw [map_add, tmulSection_add])
    (by
      intro r s t
      rw [Hom.app_smul]
      change tmulSection (M := F.restrict j) (N := G.restrict j) _
        (j.app U r • (show Γ(G.restrict j, j ⁻¹ᵁ U) from
          ((restrictAdjunction j).unit.app G).app U t)) =
        j.app U r • tmulSection (M := F.restrict j) (N := G.restrict j) _ _
      exact tmulSection_smul _ _ _)

set_option backward.isDefEq.respectTransparency false in
private theorem inversePairing_natural {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (F G : X.Modules) {U V : X.Opensᵒᵖ} (i : U ⟶ V)
    (s : Γ(F, U.unop)) (t : Γ(G, U.unop)) :
    inversePairing j F G V.unop (F.val.map i s) (G.val.map i t) =
      ((pushforward j).obj (F.restrict j ⊗ G.restrict j)).val.map i
        (inversePairing j F G U.unop s t) := by
  dsimp only [inversePairing, LinearMap.mk₂_apply]
  have hF := Hom.app_presheaf_map ((restrictAdjunction j).unit.app F) i.unop s
  have hG := Hom.app_presheaf_map ((restrictAdjunction j).unit.app G) i.unop t
  have ht := tmulSection_map (M := F.restrict j) (N := G.restrict j)
    (leOfHom ((TopologicalSpace.Opens.map j.base).map i.unop))
    (((restrictAdjunction j).unit.app F).app U.unop s)
    (((restrictAdjunction j).unit.app G).app U.unop t)
  simp only [homOfLE_leOfHom] at ht
  exact (congrArg₂ (tmulSection (M := F.restrict j) (N := G.restrict j)) hF hG).trans
    ht.symm

set_option backward.isDefEq.respectTransparency false in
private theorem exists_inverseTensorHom {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (F G : X.Modules) :
    ∃ b : F ⊗ G ⟶ (pushforward j).obj (F.restrict j ⊗ G.restrict j),
      ∀ (U : X.Opens) (s : Γ(F, U)) (t : Γ(G, U)),
        b.app U (tmulSection s t) = inversePairing j F G U s t := by
  obtain ⟨b, hb, _⟩ := SheafOfModules.tensor_bilinear_universal X.sheaf F G
    ((pushforward j).obj (F.restrict j ⊗ G.restrict j))
    (fun U ↦ inversePairing j F G U.unop) (inversePairing_natural j F G)
  exact ⟨b, fun U s t ↦ hb (Opposite.op U) s t⟩

/-- Restriction along an open immersion commutes with the sheaf tensor product, compatibly
with the canonical pure tensor sections. -/
theorem exists_restriction_tensor_comparison {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (F G : X.Modules) :
    ∃ e : (F ⊗ G).restrict j ≅ F.restrict j ⊗ G.restrict j,
      ∀ (V : Y.Opens) (s : Γ(F.restrict j, V)) (t : Γ(G.restrict j, V)),
        ((F ⊗ G).restrictAppIso j V).hom (e.inv.app V (tmulSection s t)) =
          tmulSection ((F.restrictAppIso j V).hom s) ((G.restrictAppIso j V).hom t) := by
  -- Extend the original pure tensors on image opens to a morphism on Y.
  obtain ⟨c, hc⟩ := exists_restrictionTensorHom j F G
  -- Tensor the restriction units on X and take the adjoint to obtain the inverse.
  obtain ⟨b, hb⟩ := exists_inverseTensorHom j F G
  let d := ((restrictAdjunction j).homEquiv (F ⊗ G)
    (F.restrict j ⊗ G.restrict j)).symm b
  -- The counit restricts both factors back; the triangle identities recover them.
  have hcd : c ≫ d = 𝟙 _ := by
    apply tensor_hom_ext
    intro V s t
    rw [Hom.comp_app, ConcreteCategory.comp_apply, hc]
    dsimp only [restrictionPairing, LinearMap.mk₂_apply]
    dsimp only [d]
    rw [Adjunction.homEquiv_counit, Hom.comp_app, ConcreteCategory.comp_apply]
    change ((restrictAdjunction j).counit.app (F.restrict j ⊗ G.restrict j)).app V
      (b.app (j ''ᵁ V) (tmulSection s t)) = _
    rw [hb]
    dsimp only [inversePairing, LinearMap.mk₂_apply]
    have hF := congrArg (fun a : F.restrict j ⟶ F.restrict j ↦ a.app V s)
      ((restrictAdjunction j).left_triangle_components F)
    have hG := congrArg (fun a : G.restrict j ⟶ G.restrict j ↦ a.app V t)
      ((restrictAdjunction j).left_triangle_components G)
    simp only [Hom.comp_app, ConcreteCategory.comp_apply, Hom.id_app,
      restrictAdjunction_counit_app_app] at hF hG ⊢
    have ht := tmulSection_map (M := F.restrict j) (N := G.restrict j)
      (leOfHom (eqToHom (j.preimage_image_eq V).symm))
      (((restrictAdjunction j).unit.app F).app (j ''ᵁ V) s)
      (((restrictAdjunction j).unit.app G).app (j ''ᵁ V) t)
    simp only [homOfLE_leOfHom] at ht
    exact ht.trans (congrArg₂ (tmulSection (M := F.restrict j) (N := G.restrict j)) hF hG)
  -- Under adjunction, the other composite is restriction of a pure tensor.
  have hdc : d ≫ c = 𝟙 _ := by
    apply ((restrictAdjunction j).homEquiv (F ⊗ G) ((F ⊗ G).restrict j)).injective
    rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
    apply tensor_hom_ext
    intro U s t
    rw [Hom.comp_app, ConcreteCategory.comp_apply, hb]
    change c.app (j ⁻¹ᵁ U) (inversePairing j F G U s t) = _
    dsimp only [inversePairing, LinearMap.mk₂_apply]
    rw [hc]
    dsimp only [restrictionPairing, LinearMap.mk₂_apply]
    simp only [Adjunction.homEquiv_unit, restrictAdjunction_unit_app_app]
    exact (tmulSection_map (M := F) (N := G) (j.image_preimage_le U) s t).symm
  let e : (F ⊗ G).restrict j ≅ F.restrict j ⊗ G.restrict j :=
    ⟨d, c, hdc, hcd⟩
  refine ⟨e, ?_⟩
  intro V s t
  exact hc V s t

end AlgebraicGeometry.Scheme.Modules
