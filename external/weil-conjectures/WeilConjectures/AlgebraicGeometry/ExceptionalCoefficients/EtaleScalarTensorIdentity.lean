/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedOriginScalarComparisons
import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.EtaleScalarTensorComposition

/-! # Tensor compatibility of the fixed scalar comparisons

Source: Stacks 07A4 and 0D6D, the tensor clause of the finite-Hom domain calculation.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.ExceptionalCoefficients

private theorem derived_comp_unit
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (e : F ≅ 𝟭 C) (c : F ⋙ F ≅ F)
    (hc : c = Functor.isoWhiskerRight e F ≪≫ F.leftUnitor) :
    Functor.mapDerivedCategoryCompIso F F ≪≫
        Functor.mapDerivedCategoryNatIso c =
      Functor.isoWhiskerRight
        (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso C)
        F.mapDerivedCategory ≪≫ F.mapDerivedCategory.leftUnitor := by
  subst c
  apply Iso.ext
  simp only [Iso.trans_hom]
  rw [Functor.mapDerivedCategoryNatIso_trans]
  have hu : (Functor.mapDerivedCategoryNatIso F.leftUnitor).hom = 𝟙 _ := by
    exact Functor.mapDerivedCategoryNatIso_refl
  rw [hu, Category.comp_id]
  apply (cancel_mono (Functor.mapDerivedCategoryCompIso (𝟭 C) F).inv).mp
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_comp, Category.assoc]
  rw [Functor.mapDerivedCategoryNatIso_isoWhiskerRight,
    Iso.hom_inv_id_assoc]
  have h := Functor.mapDerivedCategoryCompIso_id_comp F
  have hh : (Functor.mapDerivedCategoryCompIso (𝟭 C) F).hom =
      Functor.whiskerRight (Functor.mapDerivedCategoryIdIso C).hom
        F.mapDerivedCategory := by
    apply (cancel_epi (Functor.mapDerivedCategoryCompIso (𝟭 C) F).inv).mp
    rw [Iso.inv_hom_id, h]
    rfl
  rw [← hh]
  have hu' : F.mapDerivedCategory.leftUnitor.hom = 𝟙 F.mapDerivedCategory := by rfl
  rw [hu']
  erw [Category.id_comp, Iso.hom_inv_id, Category.comp_id]

private theorem scalar_comp_unit
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) (A : Type (u + 1)) [CommRing A] :
    ProEtale.pbcFixedScalarExtensionComp J (RingHom.id A) (RingHom.id A)
        (RingHom.id A) (by ext; rfl) =
      Functor.isoWhiskerLeft (ProEtale.pbcFixedScalarExtension J (RingHom.id A))
        (ProEtale.normalizedOriginScalarUnit J (RingHom.id A) rfl) ≪≫
      (ProEtale.pbcFixedScalarExtension J (RingHom.id A)).rightUnitor := by
  apply Adjunction.leftAdjointCompIso_comp_id
  exact derived_comp_unit _ _ _ (by
    apply Iso.ext
    ext M U x
    rfl)

private theorem tensor_identity_from_comp
    {C : Type*} [Category C] (T : C × C ⥤ C) (F : C ⥤ C)
    (δ : T ⋙ F ≅ F.prod F ⋙ T) (z : F ≅ 𝟭 C)
    (h : ∀ U V,
      z.hom.app (F.obj (T.obj (U, V))) ≫ δ.hom.app (U, V) =
        F.map (δ.hom.app (U, V)) ≫ δ.hom.app (F.obj U, F.obj V) ≫
          T.map (Prod.mkHom (z.hom.app (F.obj U)) (z.hom.app (F.obj V))))
    (U V : C) :
    δ.hom.app (U, V) ≫ T.map (Prod.mkHom (z.hom.app U) (z.hom.app V)) =
      z.hom.app (T.obj (U, V)) := by
  let : F.Faithful := Functor.Faithful.of_iso z.symm
  have hz (W : C) : z.hom.app (F.obj W) = F.map (z.hom.app W) := by
    apply (cancel_mono (z.hom.app W)).mp
    exact (z.hom.naturality (z.hom.app W)).symm
  have hn := δ.hom.naturality (Prod.mkHom (z.hom.app U) (z.hom.app V))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  have hc := h U V
  rw [hz, hz, hz] at hc
  rw [← hn, ← F.map_comp_assoc] at hc
  exact F.map_injective ((cancel_mono (δ.hom.app (U, V))).mp hc).symm

end AlgebraicGeometry.Etale.ExceptionalCoefficients
