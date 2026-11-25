/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarUnitInsertion
import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroAdjoint
import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidalPresheaf

/-! Composition of the normalized regular scalar units. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

private theorem restriction_unit_comp
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (T : Scheme.{u}) :
    Functor.LaxMonoidal.ε (Sheaf.restrictScalars T.smallEtaleTopology (ψ.comp φ)) =
      Functor.LaxMonoidal.ε (Sheaf.restrictScalars T.smallEtaleTopology φ) ≫
        (Sheaf.restrictScalars T.smallEtaleTopology φ).map
          (Functor.LaxMonoidal.ε (Sheaf.restrictScalars T.smallEtaleTopology ψ)) ≫
        (Sheaf.restrictScalarsCompIso T.smallEtaleTopology φ ψ (ψ.comp φ) rfl).hom.app
          (𝟙_ _) := by
  have hc : (Sheaf.restrictScalarsCompIso T.smallEtaleTopology φ ψ
      (ψ.comp φ) rfl).hom.app (𝟙_ _) = 𝟙 _ := by
    rfl
  rw [hc]
  erw [Category.comp_id]
  symm
  apply Sheaf.hom_ext_of_ε_comp
  have h₁ := Sheaf.ε_sheafToPresheaf_comp_map_ε_sheafCompose T.smallEtaleTopology
    (ModuleCat.restrictScalars.{u + 1} (ψ.comp φ))
  have h₂ := Sheaf.ε_sheafToPresheaf_comp_map_ε_sheafCompose T.smallEtaleTopology
    (ModuleCat.restrictScalars.{u + 1} φ)
  have h₃ := Sheaf.ε_sheafToPresheaf_comp_map_ε_sheafCompose T.smallEtaleTopology
    (ModuleCat.restrictScalars.{u + 1} ψ)
  simp only [Functor.map_comp]
  rw [h₁, reassoc_of% h₂]
  rw [show (sheafToPresheaf _ _).map ((sheafCompose _
      (ModuleCat.restrictScalars.{u + 1} φ)).map
        (Functor.LaxMonoidal.ε (sheafCompose T.smallEtaleTopology
          (ModuleCat.restrictScalars.{u + 1} ψ)))) =
      ((Functor.whiskeringRight _ _ _).obj (ModuleCat.restrictScalars.{u + 1} φ)).map
        ((sheafToPresheaf _ _).map (Functor.LaxMonoidal.ε
          (sheafCompose T.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} ψ)))) from rfl,
    ← Functor.map_comp, h₃]
  have key : Functor.LaxMonoidal.ε ((Functor.whiskeringRight T.Etaleᵒᵖ _ _).obj
        (ModuleCat.restrictScalars.{u + 1} φ)) ≫
      ((Functor.whiskeringRight T.Etaleᵒᵖ _ _).obj
        (ModuleCat.restrictScalars.{u + 1} φ)).map
        (Functor.LaxMonoidal.ε ((Functor.whiskeringRight T.Etaleᵒᵖ _ _).obj
          (ModuleCat.restrictScalars.{u + 1} ψ))) =
      Functor.LaxMonoidal.ε ((Functor.whiskeringRight T.Etaleᵒᵖ _ _).obj
        (ModuleCat.restrictScalars.{u + 1} (ψ.comp φ))) := by
    ext U : 2
    apply ModuleCat.hom_ext
    ext
    simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
    erw [ModuleCat.restrictScalars_η, ModuleCat.restrictScalars_η,
      ModuleCat.restrictScalars_η]
    rfl
  rw [Functor.map_comp, ← Category.assoc]
  erw [key]
  rfl

private theorem unit_comp_transport
    {CA CB CC : Type*} [Category CA] [Category CB] [Category CC]
    (F : CA ⥤ CB) (G : CB ⥤ CC) (H : CA ⥤ CC) (α : F ⋙ G ≅ H)
    {A A' : CA} {B B' : CB} {C C' : CC}
    (i : A ≅ A') (j : B ≅ B') (k : C ≅ C')
    (a : F.obj A' ⟶ B') (b : G.obj B' ⟶ C') (c : H.obj A' ⟶ C')
    (h : G.map (F.map i.hom ≫ a ≫ j.inv) ≫ (G.map j.hom ≫ b ≫ k.inv) =
      α.hom.app A ≫ (H.map i.hom ≫ c ≫ k.inv)) :
    G.map a ≫ b = α.hom.app A' ≫ c := by
  have hn := α.hom.naturality i.hom
  dsimp only [Functor.comp_map] at hn
  have hj : G.map j.inv ≫ G.map j.hom = 𝟙 _ := by
    rw [← G.map_comp, j.inv_hom_id, G.map_id]
  simp only [Functor.map_comp, Category.assoc] at h
  rw [reassoc_of% hj] at h
  apply (cancel_epi ((F ⋙ G).map i.hom)).1
  apply (cancel_mono k.inv).1
  dsimp only [Functor.comp_map]
  simp only [Category.assoc]
  rw [reassoc_of% hn]
  exact h

/-- The regular scalar units compose through the fixed derived scalar compositor.
Source: finite-dualizing normalization, paragraphs 1--3 and the final sentence.
Proof: on presheaf sections the ordinary restriction units compose by composition
of the coefficient ring maps; the sheaf unit comparison gives the same equality
for sheaves. Identify each regular derived unit with the exact-single adjunction
insertion of its ordinary unit. The insertion composition formula gives the fixed
left-adjoint compositor. Naturality transports this equation from single objects
back to the derived tensor units.
(blueprint: lem-coef-etale-scalar-unit-composition) -/
theorem normalizedScalarUnit_comp
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (hχ : χ = ψ.comp φ)
    (T : Scheme.{u}) :
    (Etale.scalarExtension ψ T).map (Etale.ExceptionalCoefficients.unitIso φ T).hom ≫
      (Etale.ExceptionalCoefficients.unitIso ψ T).hom =
    (ProEtale.pbcFixedScalarExtensionComp T.smallEtaleTopology φ ψ χ hχ).hom.app
      (Etale.constantComplex A T) ≫ (Etale.ExceptionalCoefficients.unitIso χ T).hom := by
  subst χ
  apply unit_comp_transport (Etale.scalarExtension φ T) (Etale.scalarExtension ψ T)
    (Etale.scalarExtension (ψ.comp φ) T)
    (ProEtale.pbcFixedScalarExtensionComp T.smallEtaleTopology φ ψ (ψ.comp φ) rfl)
    (_root_.DerivedCategory.singleFunctorObjUnitIso
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (_root_.DerivedCategory.singleFunctorObjUnitIso
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (_root_.DerivedCategory.singleFunctorObjUnitIso
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} C)))
  rw [Etale.scalarUnit_eq_adjointInsertion, Etale.scalarUnit_eq_adjointInsertion,
    Etale.scalarUnit_eq_adjointInsertion]
  exact SheafExactDegreeZero.adjointInsertion_comp
    (Sheaf.restrictScalars T.smallEtaleTopology φ)
    (Sheaf.restrictScalars T.smallEtaleTopology ψ)
    (Sheaf.restrictScalars T.smallEtaleTopology (ψ.comp φ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology ψ))
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology (ψ.comp φ)))
    (Sheaf.restrictScalarsCompIso T.smallEtaleTopology φ ψ (ψ.comp φ) rfl)
    (Functor.LaxMonoidal.ε (Sheaf.restrictScalars T.smallEtaleTopology φ))
    (Functor.LaxMonoidal.ε (Sheaf.restrictScalars T.smallEtaleTopology ψ))
    (Functor.LaxMonoidal.ε (Sheaf.restrictScalars T.smallEtaleTopology (ψ.comp φ)))
    (restriction_unit_comp φ ψ T)

end AlgebraicGeometry.Etale
