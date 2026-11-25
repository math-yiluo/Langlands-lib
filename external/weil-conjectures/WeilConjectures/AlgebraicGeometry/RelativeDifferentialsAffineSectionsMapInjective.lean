/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeDifferentialsAffineSectionsMap
import WeilConjectures.AlgebraicGeometry.RelativeDifferentialsAffineChartDerivation

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry
variable {X S : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The affine comparison map is injective by the uniqueness part of the universal
property of Kähler differentials. Apply the affine Spec comparison to identify the
target with the module of Kähler differentials, then use uniqueness of maps preserving
the universal derivation. Source: Stacks Project, Tag 01UT.
(blueprint: lem-sc-relative-differentials-affine-sections-map-injective). -/
theorem relativeDifferentials_affine_sections_map_injective (f : X ⟶ S)
    (U : X.affineOpens) (V : S.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (e : CommRingCat.KaehlerDifferential (f.appLE V.1 U.1 hUV) →ₗ[Γ(X, U.1)]
      Γ(f.relativeDifferentials, U.1))
    (he : ∀ a : Γ(X, U.1), e (CommRingCat.KaehlerDifferential.d a) =
      f.relativeDifferentialsDerivation.d (X := op U.1) a) : Function.Injective e := by
  let φ := f.appLE V.1 U.1 hUV
  obtain ⟨T, _, hd⟩ := relativeDifferentials_affine_chart_derivation f U V hUV
  have hW : U.1 ≤ U.2.fromSpec ''ᵁ ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, U.2.opensRange_fromSpec]
  have hid : (homOfLE (U.2.fromSpec_image_le ⊤)).op ≫ (homOfLE hW).op =
      𝟙 (op U.1) := Subsingleton.elim _ _
  let L : (moduleSpecΓFunctor.obj (f.relativeDifferentials.restrict U.2.fromSpec)) →ₗ[Γ(X, U.1)]
      Γ(f.relativeDifferentials, U.1) :=
    { toFun := fun z ↦ f.relativeDifferentials.presheaf.map (homOfLE hW).op
        ((f.relativeDifferentials.restrictAppIso U.2.fromSpec ⊤).hom z)
      map_add' := by intros; simp
      map_smul' := by
        intro r z
        rw [Scheme.Modules.restrictAppIso_fromSpec_smul, Scheme.Modules.map_smul]
        rw [← Functor.map_comp_apply, hid]
        simp only [CategoryTheory.Functor.map_id, ConcreteCategory.id_apply, RingHom.id_apply] }
  let C := L.comp ((moduleSpecΓFunctor.map T.inv).hom.comp
    (relativeDifferentialsSpecΓHom φ).hom)
  have hgen (a : Γ(X, U.1)) : C (CommRingCat.KaehlerDifferential.d a) =
      f.relativeDifferentialsDerivation.d a := by
    change f.relativeDifferentials.presheaf.map (homOfLE hW).op
      ((f.relativeDifferentials.restrictAppIso U.2.fromSpec ⊤).hom
        ((moduleSpecΓFunctor.map T.inv).hom
          ((relativeDifferentialsSpecΓHom φ).hom (CommRingCat.KaehlerDifferential.d a)))) = _
    rw [relativeDifferentialsSpecΓHom_d]
    change f.relativeDifferentials.presheaf.map (homOfLE hW).op
      (T.inv.val.app (op ⊤) ((Spec.map φ).relativeDifferentialsDerivation.d
        ((Scheme.ΓSpecIso Γ(X, U.1)).inv a))) = _
    rw [hd]
    change f.relativeDifferentials.val.map (homOfLE hW).op
      (f.relativeDifferentialsDerivation.d _) = _
    refine (f.relativeDifferentialsDerivation.d_map (homOfLE hW).op
      ((U.2.fromSpec.appIso ⊤).inv ((Scheme.ΓSpecIso Γ(X, U.1)).inv a))).symm.trans ?_
    apply congrArg f.relativeDifferentialsDerivation.d
    have hr : (U.2.fromSpec.appIso ⊤).inv ((Scheme.ΓSpecIso Γ(X, U.1)).inv a) =
        X.presheaf.map (homOfLE (U.2.fromSpec_image_le ⊤)).op a := by
      have ht : (TopologicalSpace.Opens.leTop
          (⊤ : (Spec Γ(X, U.1)).Opens)).op = 𝟙 (op ⊤) := Subsingleton.elim _ _
      simpa only [ConcreteCategory.comp_apply, ht, CategoryTheory.Functor.map_id,
        ConcreteCategory.id_apply] using
          ConcreteCategory.congr_hom (U.2.ΓSpecIso_inv_map_appIso_inv ⊤) a
    change X.presheaf.map (homOfLE hW).op
      ((U.2.fromSpec.appIso ⊤).inv ((Scheme.ΓSpecIso Γ(X, U.1)).inv a)) = a
    rw [hr, ← Functor.map_comp_apply, hid]
    exact ConcreteCategory.congr_hom (X.presheaf.map_id (op U.1)) a
  have heC : ModuleCat.ofHom e = ModuleCat.ofHom C := by
    apply CommRingCat.KaehlerDifferential.ext
    intro a
    exact (he a).trans (hgen a).symm
  have hf (x : CommRingCat.KaehlerDifferential φ) : e x = C x :=
    ConcreteCategory.congr_hom heC x
  have hL : Function.Injective L := by
    intro z w hzw
    apply (ConcreteCategory.bijective_of_isIso
      (f.relativeDifferentials.restrictAppIso U.2.fromSpec ⊤).hom).1
    have hid' : (homOfLE hW).op ≫ (homOfLE (U.2.fromSpec_image_le ⊤)).op =
        𝟙 (op (U.2.fromSpec ''ᵁ ⊤)) := Subsingleton.elim _ _
    have h := congrArg
      (f.relativeDifferentials.presheaf.map (homOfLE (U.2.fromSpec_image_le ⊤)).op) hzw
    change f.relativeDifferentials.presheaf.map (homOfLE (U.2.fromSpec_image_le ⊤)).op
      (f.relativeDifferentials.presheaf.map (homOfLE hW).op
        ((f.relativeDifferentials.restrictAppIso U.2.fromSpec ⊤).hom z)) =
      f.relativeDifferentials.presheaf.map (homOfLE (U.2.fromSpec_image_le ⊤)).op
        (f.relativeDifferentials.presheaf.map (homOfLE hW).op
          ((f.relativeDifferentials.restrictAppIso U.2.fromSpec ⊤).hom w)) at h
    simpa only [← Functor.map_comp_apply, hid', f.relativeDifferentials.presheaf.map_id,
      ConcreteCategory.id_apply] using h
  intro x y hxy
  apply (ConcreteCategory.bijective_of_isIso (relativeDifferentialsSpecΓHom φ)).1
  apply (ConcreteCategory.bijective_of_isIso (moduleSpecΓFunctor.map T.inv)).1
  apply hL
  exact (hf x).symm.trans (hxy.trans (hf y))
end AlgebraicGeometry
