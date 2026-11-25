/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SignedLineDerivedBaseChange.SignedLineDerivedBaseChangeData
import WeilConjectures.Algebra.Homology.SignedLineDerivedBaseChange.FlatLineResolvingNormalization

/-! # Localization of an exact tensor action -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u v w z
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace SheafOfModules.SignedLineDerivedBaseChange

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {U : C ⥤ D} [U.IsContinuous J K]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [HasWeakSheafify K AddCommGrpCat.{max u v w}]
  {R : Sheaf J CommRingCat.{max u v w}}
  {S : Sheaf K CommRingCat.{max u v w}}

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})] in
/-- Localizing a tensor comparison with flat fixed factors gives a unique derived action.
Source: Stacks Project, Tags 06YU, 07A4 and 015F.
(blueprint: lem-pur-flat-tensor-derived-action)
Proof: compose the two flat-factor resolving comparisons, the exact functor
factorization and the termwise tensor comparison. This gives an isomorphism after
precomposition with the cochain localization. Lift it uniquely through that
localization. Cancellation of the two resolving comparisons gives the displayed
square. The same cancellation and full faithfulness of localization whiskering
prove uniqueness. No boundedness hypothesis is used. -/
theorem flat_tensor_derived_action
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules R)]
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules S)]
    (F : KFlatFixedTensor.Modules R ⥤ KFlatFixedTensor.Modules S)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : KFlatFixedTensor.Modules R) (M : KFlatFixedTensor.Modules S)
    (hL : IsFlatOnSite (J := J) (R := R) L)
    (hM : IsFlatOnSite (J := K) (R := S) M)
    (γ : siteSheafTensorRight L ⋙ F ≅ F ⋙ siteSheafTensorRight M) :
    ∃ b : DerivedActionData F L M, DerivedAction F L M γ b := by
  obtain ⟨hLK, hLF, cR, hcR⟩ := flat_line_resolving_normalization R L hL
  obtain ⟨hMK, hMF, cS, hcS⟩ := flat_line_resolving_normalization S M hM
  let ψ : DerivedCategory.Q ⋙ derivedLine.{u, v, w, z} R L ⋙ F.mapDerivedCategory ≅
      DerivedCategory.Q ⋙ F.mapDerivedCategory ⋙ derivedLine.{u, v, w, z} S M :=
    Functor.isoWhiskerRight cR F.mapDerivedCategory ≪≫
    Functor.isoWhiskerLeft ((siteSheafTensorRight L).mapHomologicalComplex (.up ℤ))
      F.mapDerivedCategoryFactors ≪≫
    Functor.isoWhiskerRight (NatIso.mapHomologicalComplex γ (.up ℤ)) DerivedCategory.Q ≪≫
    Functor.isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ)) cS.symm ≪≫
    (Functor.isoWhiskerRight F.mapDerivedCategoryFactors
      (derivedLine.{u, v, w, z} S M)).symm
  let η : derivedLine.{u, v, w, z} R L ⋙ F.mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ derivedLine.{u, v, w, z} S M :=
    Localization.liftNatIso DerivedCategory.Q
      (HomologicalComplex.quasiIso (KFlatFixedTensor.Modules R) (.up ℤ)) _ _ _ _ ψ
  have hη (E : CochainComplex (KFlatFixedTensor.Modules R) ℤ) :
      η.hom.app (DerivedCategory.Q.obj E) = ψ.hom.app E := by
    dsimp only [η, Localization.liftNatIso]
    simp only [Localization.liftNatTrans_app, Localization.Lifting.iso]
    simp
  have hs (E : CochainComplex (KFlatFixedTensor.Modules R) ℤ) :
      η.hom.app (DerivedCategory.Q.obj E) ≫
          (derivedLine.{u, v, w, z} S M).map (F.mapDerivedCategoryFactors.hom.app E) ≫
          cS.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj E) =
        F.mapDerivedCategory.map (cR.hom.app E) ≫
          F.mapDerivedCategoryFactors.hom.app
            (((siteSheafTensorRight L).mapHomologicalComplex (.up ℤ)).obj E) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex γ (.up ℤ)).hom.app E) := by
    rw [hη]
    simp only [ψ, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Iso.symm_hom, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
      Category.assoc]
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp, Iso.inv_hom_id_app]
    exact congrArg (fun f ↦ F.mapDerivedCategory.map (cR.hom.app E) ≫
      F.mapDerivedCategoryFactors.hom.app
        (((siteSheafTensorRight L).mapHomologicalComplex (.up ℤ)).obj E) ≫ f)
      (Category.comp_id (DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex γ (.up ℤ)).hom.app E)))
  refine ⟨⟨cR, cS, η⟩, hLK, hMK, hLF, hMF, hcR, hcS,
    fun E ↦ heq_of_eq (hs E), ?_⟩
  intro η' hη'
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (KFlatFixedTensor.Modules R) (.up ℤ))
  intro E
  apply (cancel_mono ((derivedLine.{u, v, w, z} S M).map
    (F.mapDerivedCategoryFactors.hom.app E) ≫
      cS.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj E))).mp
  exact (eq_of_heq (hη' E)).trans (hs E).symm

end SheafOfModules.SignedLineDerivedBaseChange
