/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralResidueTensorPullPresentation

/-! The normalized middle composite for the residue tensor-pull counit.

Source: Bhatt--Scholze, Remark 6.8.15 and the proof of Lemma 6.5.9(5), p. 51.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe v u u₁ u₂
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
attribute [local instance] CategoryTheory.derivedTensorPresentationBraiding
noncomputable section GenericNormalization
variable {C : Type u₁} [Category.{v + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{v + 1} C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]

private theorem tensorPresentation_fac (B : C)
    (H : DerivedCategory C ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ H ⟶
      (tensorLeft B).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [H.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (.up ℤ))]
    (P : HomotopyCategory C (.up ℤ)) :
    (derivedTensorPresentationIso B H ε).hom.app (DerivedCategory.Qh.obj P) ≫
      (β_ ((DerivedCategory.singleFunctor C 0).obj B) (DerivedCategory.Qh.obj P)).inv ≫
      (Functor.tensorModelCoefficientIso B).hom ▷ DerivedCategory.Qh.obj P ≫
      Functor.LaxMonoidal.μ DerivedCategory.Qh (Functor.tensorModelCoefficient B) P =
      ε.app P ≫ DerivedCategory.Qh.map ((homotopyTensorSingleIso B).inv.app P) := by
  simpa only [Functor.tensorModelCoefficientIso] using
    derivedTensorPresentationIso_fac B H ε P

variable {D : Type u₂} [Category.{v + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{v + 1} D] [MonoidalCategory D] [MonoidalClosed D]
  [MonoidalPreadditive D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]

omit [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C]
  [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C] in
set_option backward.isDefEq.respectTransparency false in
private theorem tensorPullCounit_fac_private (F : C ⥤ D) [F.Additive]
    (G : DerivedCategory C ⥤ DerivedCategory D)
    (γ : DerivedCategory.Qh ⋙ G ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (B : C) (B' : D)
    (c : G.obj ((DerivedCategory.singleFunctor C 0).obj B) ≅
      (DerivedCategory.singleFunctor D 0).obj B')
    (eH : (F.mapHomotopyCategory (.up ℤ)).obj (Functor.tensorModelCoefficient B) ≅
      Functor.tensorModelCoefficient B')
    (hc : c.inv ≫ G.map (Functor.tensorModelCoefficientIso B).hom ≫
      γ.app (Functor.tensorModelCoefficient B) =
        (Functor.tensorModelCoefficientIso B').hom ≫ DerivedCategory.Qh.map eH.inv)
    (H : DerivedCategory D ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ H ⟶
      (tensorLeft B').mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [H.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso D (.up ℤ))]
    (P : HomotopyCategory C (.up ℤ)) :
    (derivedTensorPresentationIso B' H ε).hom.app
        (G.obj (DerivedCategory.Qh.obj P)) ≫
      ((curriedTensor (DerivedCategory D)).flip.mapIso c.symm).hom.app
        (G.obj (DerivedCategory.Qh.obj P)) ≫
      Functor.tensorModelTargetWith F G γ B P =
      H.map (γ.app P) ≫
        ε.app ((F.mapHomotopyCategory (.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map
          ((homotopyTensorSingleIso B').inv.app ((F.mapHomotopyCategory (.up ℤ)).obj P) ≫
            eH.inv ▷ (F.mapHomotopyCategory (.up ℤ)).obj P) := by
  unfold Functor.tensorModelTargetWith
  simp only [Functor.mapIso_hom, Functor.flip_map_app,
    curriedTensor_obj_map, Iso.symm_hom]
  erw [BraidedCategory.braiding_inv_naturality_right_assoc]
  simp only [MonoidalCategory.tensorHom_def, Category.assoc]
  rw [← comp_whiskerRight_assoc]
  rw [hc]
  simp only [comp_whiskerRight, Category.assoc]
  rw [← whisker_exchange_assoc, ← whisker_exchange_assoc,
    ← BraidedCategory.braiding_inv_naturality_left_assoc]
  have hn := (derivedTensorPresentationIso B' H ε).hom.naturality
    (γ.app P)
  dsimp only [Functor.comp_map, Functor.flip_obj_map, curriedTensor_map_app] at hn
  erw [← reassoc_of% hn]
  erw [Functor.LaxMonoidal.μ_natural_left]
  simp only [Functor.map_comp]
  erw [reassoc_of% tensorPresentation_fac B' H ε
    ((F.mapHomotopyCategory (.up ℤ)).obj P)]

/-- Public export of the private `tensorPullCounit_fac_private`
(used by `import all` importers; linter.privateModule). -/
alias tensorPullCounit_fac := tensorPullCounit_fac_private

end GenericNormalization
local instance instEssentiallySmallProfinite_algebraicGeometryIntegralResidueTensorPullCounitCore
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

attribute [local instance 20000] sheafBraidedCategory
attribute [local instance 20000] Functor.tensorModelHomotopyMonoidal
attribute [local irreducible] Functor.leftDerivedFunctor Functor.mapDerivedCategory
end AlgebraicGeometry.ProEtale.CondensedRing
