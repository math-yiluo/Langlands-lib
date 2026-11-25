/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Native.NativeDerivedHomSignedExact
public import WeilConjectures.CategoryTheory.Exact.ExactClosedDerivedHom
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal

/-! # Signed shift compatibility of exact derived closed comparisons

Source: Stacks Project, Tags 08J9, 08JC and 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false
universe u v w c d
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite
open AlgebraicGeometry.ProEtale CategoryTheory.MonoidalClosed

namespace CategoryTheory.Functor

-- Naturality of taking mates turns a square of tensor maps into a square of Hom maps.
private theorem mate_naturality
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ R₁ R₂ : C ⥤ C} {L₃ L₄ R₃ R₄ : D ⥤ D}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃) (a₄ : L₄ ⊣ R₄)
    (G : C ⥤ D) (α : L₂ ⟶ L₁) (δ : L₄ ⟶ L₃)
    (t₁ : TwoSquare G L₁ L₃ G) (t₂ : TwoSquare G L₂ L₄ G)
    (h : t₂.whiskerLeft α = t₁.whiskerRight δ) :
    whiskerRight (conjugateEquiv a₁ a₂ α) G ≫ (mateEquiv a₂ a₄ t₂) =
      (mateEquiv a₁ a₃ t₁) ≫ whiskerLeft G (conjugateEquiv a₃ a₄ δ) := by
  have hh := congrArg (mateEquiv a₁ a₄) h
  rw [conjugateEquiv_mateEquiv_vcomp, mateEquiv_conjugateEquiv_vcomp] at hh
  exact hh

private theorem sourceShift_conjugate
    {C : Type u} [Category.{v} C] [Preadditive C] [HasShift C ℤ]
    [MonoidalCategory C] [MonoidalClosed C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [(curriedTensor C).CommShift₂Int]
    (K : C) (n : ℤ) :
    (siteHomSourceShift K n).hom =
      conjugateEquiv (ihom.adjunction (K⟦n⟧))
        ((shiftEquiv C n).toAdjunction.comp (ihom.adjunction K))
        (((tensorLeft K).commShiftIso n ≪≫ (siteHomTensorParameterShift K n).symm).hom) := by
  unfold siteHomSourceShift Adjunction.rightAdjointUniq
  ext M
  simp [conjugateEquiv_apply_app, Adjunction.ofNatIsoLeft_unit]

-- The mate of the inverse shift comparison is the comparison for the inverse shift.
private theorem shift_mate
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    (G : C ⥤ D) [G.CommShift ℤ] (n : ℤ) :
    (mateEquiv (shiftEquiv C n).toAdjunction (shiftEquiv D n).toAdjunction
      ((G.commShiftIso n).inv)) = (G.commShiftIso (-n)).hom := by
  ext M
  have h : (shiftFunctorCompIsoId D n (-n) (add_neg_cancel n)).inv.app
        (G.obj ((shiftFunctor C (-n)).obj M)) ≫
      (shiftFunctor D (-n)).map ((shiftFunctor D n).map
        ((G.commShiftIso (-n)).hom.app M)) ≫
      (shiftFunctor D (-n)).map
        ((shiftFunctorCompIsoId D (-n) n (neg_add_cancel n)).hom.app (G.obj M)) =
      (G.commShiftIso (-n)).hom.app M := by
    have hn := (shiftFunctorCompIsoId D n (-n) (add_neg_cancel n)).inv.naturality
      ((G.commShiftIso (-n)).hom.app M)
    dsimp at hn
    rw [← reassoc_of% hn]
    have ht := (shiftEquiv D n).toAdjunction.right_triangle_components (G.obj M)
    dsimp [Equivalence.toAdjunction, shiftEquiv, shiftEquiv'] at ht
    calc
      _ = (G.commShiftIso (-n)).hom.app M ≫ 𝟙 _ :=
        congrArg (fun f ↦ (G.commShiftIso (-n)).hom.app M ≫ f) ht
      _ = _ := Category.comp_id _
  simpa [mateEquiv, shiftEquiv'] using h

section Generic
variable {C : Type u} {D : Type w} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D] [HasShift C ℤ] [HasShift D ℤ]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalClosed C] [MonoidalClosed D]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [(curriedTensor C).CommShift₂Int] [(curriedTensor D).CommShift₂Int]
  (G : C ⥤ D) [G.CommShift ℤ] [G.LaxMonoidal]

-- Take mates of the tensor interchange square, using the definition of the source shift.
private theorem sourceShift_comparison (K M : C) (n : ℤ)
    (ht : ∀ X : C,
      G.obj K ◁ (G.commShiftIso n).inv.app X ≫ LaxMonoidal.μ G K (X⟦n⟧) ≫
        G.map (((tensorLeft K).commShiftIso n ≪≫
          (siteHomTensorParameterShift K n).symm).hom.app X) =
      (((tensorLeft (G.obj K)).commShiftIso n ≪≫
        (siteHomTensorParameterShift (G.obj K) n).symm).hom.app (G.obj X)) ≫
        ((G.commShiftIso n).inv.app K ▷ G.obj X) ≫ LaxMonoidal.μ G (K⟦n⟧) X) :
    G.map ((siteHomSourceShift K n).hom.app M) ≫
        (G.commShiftIso (-n)).hom.app ((ihom K).obj M) ≫
        ((LaxMonoidal.ihomComparison G K).app M)⟦-n⟧' =
      (LaxMonoidal.ihomComparison G (K⟦n⟧)).app M ≫
        (pre ((G.commShiftIso n).inv.app K)).app (G.obj M) ≫
        (siteHomSourceShift (G.obj K) n).hom.app (G.obj M) := by
  let eC := (tensorLeft K).commShiftIso n ≪≫ (siteHomTensorParameterShift K n).symm
  let eD := (tensorLeft (G.obj K)).commShiftIso n ≪≫
    (siteHomTensorParameterShift (G.obj K) n).symm
  let aC := (shiftEquiv C n).toAdjunction.comp (ihom.adjunction K)
  let aD := (shiftEquiv D n).toAdjunction.comp (ihom.adjunction (G.obj K))
  let t := TwoSquare.vComp ((G.commShiftIso n).inv) (LaxMonoidal.μTwoSquare G K)
  have h := mate_naturality (ihom.adjunction (K⟦n⟧)) aC
    (ihom.adjunction (G.obj (K⟦n⟧))) aD G eC.hom
    (eD.hom ≫ (curriedTensor D).map ((G.commShiftIso n).inv.app K))
    (LaxMonoidal.μTwoSquare G (K⟦n⟧)) t (by
      ext X
      dsimp [t, TwoSquare.vComp, TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
        eC, eD, LaxMonoidal.μTwoSquare]
      simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        Category.id_comp, Category.comp_id, Category.assoc] using ht X)
  have hc : conjugateEquiv (ihom.adjunction (K⟦n⟧)) aC eC.hom =
      (siteHomSourceShift K n).hom := (sourceShift_conjugate K n).symm
  have hd : conjugateEquiv (ihom.adjunction (G.obj (K⟦n⟧))) aD
      (eD.hom ≫ (curriedTensor D).map ((G.commShiftIso n).inv.app K)) =
      pre ((G.commShiftIso n).inv.app K) ≫ (siteHomSourceShift (G.obj K) n).hom := by
    erw [← conjugateEquiv_comp _ (ihom.adjunction ((G.obj K)⟦n⟧))]
    rw [← sourceShift_conjugate]
    rfl
  rw [hc, hd] at h
  change whiskerRight (siteHomSourceShift K n).hom G ≫
    (mateEquiv ((shiftEquiv C n).toAdjunction.comp (ihom.adjunction K))
      ((shiftEquiv D n).toAdjunction.comp (ihom.adjunction (G.obj K))) t) = _ at h
  rw [show t = TwoSquare.vComp ((G.commShiftIso n).inv)
    (LaxMonoidal.μTwoSquare G K) from rfl, mateEquiv_hcomp] at h
  have hs : mateEquiv (shiftEquiv C n).toAdjunction (shiftEquiv D n).toAdjunction
      (G.commShiftIso n).inv = (G.commShiftIso (-n)).hom := shift_mate G n
  rw [hs] at h
  have hh := NatTrans.congr_app h M
  dsimp only [TwoSquare.hComp, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    associator_hom_app, associator_inv_app] at hh
  simpa only [shiftEquiv'_inverse, Functor.comp_obj,
    LaxMonoidal.ihomComparison, Category.id_comp, Category.comp_id, Category.assoc] using hh
end Generic
section Derived
open CategoryTheory.Limits
variable {C : Type u} [Category.{v + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{v + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [MonoidalClosed C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
  {D : Type w} [Category.{v + 1} D] [Abelian D] [IsGrothendieckAbelian.{v + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]

-- The existing derived tensor comparison is shift-compatible in either variable.
private abbrev comparisonFlip (K : DerivedCategory C) :
    tensorRight K ⋙ F.mapDerivedCategory ⟶
      F.mapDerivedCategory ⋙ tensorRight (F.mapDerivedCategory.obj K) :=
  F.mapDerivedCategoryTensorComparison.flipApp K

private theorem comparison_flip_of_iso {K K' : DerivedCategory C} (e : K ≅ K')
    [NatTrans.CommShift (comparisonFlip F K') ℤ] :
    NatTrans.CommShift (comparisonFlip F K) ℤ := by
  have he : comparisonFlip F K =
      whiskerRight ((curriedTensor _).flip.map e.hom) F.mapDerivedCategory ≫
        comparisonFlip F K' ≫
        whiskerLeft F.mapDerivedCategory
          ((curriedTensor _).flip.map (F.mapDerivedCategory.map e.inv)) := by
    ext X
    have h := (F.mapDerivedCategoryTensorComparison.app X).naturality e.hom
    dsimp at h ⊢
    rw [reassoc_of% h, ← MonoidalCategory.whiskerLeft_comp,
      ← F.mapDerivedCategory.map_comp, e.hom_inv_id, F.mapDerivedCategory.map_id,
      MonoidalCategory.whiskerLeft_id, Category.comp_id]
  rw [he]
  infer_instance

private theorem comparison_flip_Qh (X : HomotopyCategory C (.up ℤ))
    (hX : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat X) (hFX : F.kFlatMap X) :
    NatTrans.CommShift (comparisonFlip F (DerivedCategory.Qh.obj X)) ℤ := by
  apply DerivedCategory.commShift_of_tensorRight_fac F F.mapDerivedCategory
    F.mapDerivedCategoryFactorsh.hom X hX hFX
  intro M
  have h := F.mapDerivedCategoryTensorComparison_app_app_comp M X
  rw [MonoidalCategory.tensorHom_def, Category.assoc] at h
  exact h

private theorem comparison_flip (K : DerivedCategory C) :
    NatTrans.CommShift (comparisonFlip F K) ℤ := by
  let Λ := (inferInstance : Abelian.HasFunctorialFlatResolution C).some.reduced
  let K₀ := DerivedCategory.Q.objPreimage K
  let R := Λ.resolutionFunctor.obj K₀
  have hR := Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K₀
  have hFR := F.kFlatMap_quotient_obj_resolutionFunctor_obj Λ K₀
  haveI := comparison_flip_Qh F ((HomotopyCategory.quotient C (.up ℤ)).obj R)
    ((HomotopyCategory.kFlat_quotient_obj_iff _).2 hR) hFR
  let e : K ≅ DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj R) :=
    (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
      (asIso (DerivedCategory.Q.map (Λ.resolutionNatTrans.app K₀))).symm ≪≫
      (DerivedCategory.quotientCompQhIso C).symm.app R
  exact comparison_flip_of_iso F e

private theorem exactDerived_δ (K M : DerivedCategory C) :
    letI := exactClosedDerivedMonoidal F
    OplaxMonoidal.δ F.mapDerivedCategory K M =
      (F.mapDerivedCategoryTensorComparison.app K).app M := by
  unfold exactClosedDerivedMonoidal
  letI := F.residueDerivedMonoidal
  rw [Monoidal.transport_δ]
  rfl

-- Combine the two tensor shift squares and cancel the strong monoidal comparisons.
private theorem tensor_interchange (K X : DerivedCategory C) (n : ℤ) :
    letI := exactClosedDerivedMonoidal F
    F.mapDerivedCategory.obj K ◁ (F.mapDerivedCategory.commShiftIso n).inv.app X ≫
        LaxMonoidal.μ F.mapDerivedCategory K (X⟦n⟧) ≫
        F.mapDerivedCategory.map (((tensorLeft K).commShiftIso n ≪≫
          (siteHomTensorParameterShift K n).symm).hom.app X) =
      (((tensorLeft (F.mapDerivedCategory.obj K)).commShiftIso n ≪≫
        (siteHomTensorParameterShift (F.mapDerivedCategory.obj K) n).symm).hom.app
          (F.mapDerivedCategory.obj X)) ≫
        ((F.mapDerivedCategory.commShiftIso n).inv.app K ▷ F.mapDerivedCategory.obj X) ≫
        LaxMonoidal.μ F.mapDerivedCategory (K⟦n⟧) X := by
  let G := F.mapDerivedCategory
  letI := exactClosedDerivedMonoidal F
  haveI := comparison_flip F X
  have hL := NatTrans.shift_app_comm (F.mapDerivedCategoryTensorComparisonApp K) n X
  have hR := NatTrans.shift_app_comm (comparisonFlip F X) n K
  simp only [Functor.commShiftIso_comp_hom_app] at hL hR
  dsimp at hL hR
  have hL' : G.map (((tensorLeft K).commShiftIso n).hom.app X) ≫
        (G.commShiftIso n).hom.app (K ⊗ X) ≫ (OplaxMonoidal.δ G K X)⟦n⟧' =
      OplaxMonoidal.δ G K (X⟦n⟧) ≫ G.obj K ◁ (G.commShiftIso n).hom.app X ≫
        ((tensorLeft (G.obj K)).commShiftIso n).hom.app (G.obj X) := by
    dsimp only [G]
    rw [exactDerived_δ F, exactDerived_δ F]
    simpa only [Category.assoc] using hL
  have hR' : G.map (((tensorRight X).commShiftIso n).hom.app K) ≫
        (G.commShiftIso n).hom.app (K ⊗ X) ≫ (OplaxMonoidal.δ G K X)⟦n⟧' =
      OplaxMonoidal.δ G (K⟦n⟧) X ≫ (G.commShiftIso n).hom.app K ▷ G.obj X ≫
        ((tensorRight (G.obj X)).commShiftIso n).hom.app (G.obj K) := by
    dsimp only [G]
    rw [exactDerived_δ F, exactDerived_δ F]
    simpa only [Category.assoc] using hR
  apply (cancel_epi (OplaxMonoidal.δ G K (X⟦n⟧) ≫
    G.obj K ◁ (G.commShiftIso n).hom.app X)).mp
  apply (cancel_mono (OplaxMonoidal.δ G (K⟦n⟧) X ≫
    (G.commShiftIso n).hom.app K ▷ G.obj X ≫
      ((tensorRight (G.obj X)).commShiftIso n).hom.app (G.obj K))).mp
  dsimp only [G, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  simp only [siteHomTensorParameterShift, NatIso.ofComponents_inv_app, Iso.app_inv,
    Functor.map_comp, Category.assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    Iso.hom_inv_id_app, Category.id_comp, Monoidal.μ_δ_assoc,
    ← comp_whiskerRight_assoc, Iso.inv_hom_id_app, id_whiskerRight]
  rw [← hR']
  dsimp only [G, Functor.comp_obj] at hL' hR' ⊢
  simp only [MonoidalCategory.whiskerLeft_id, Category.id_comp, Monoidal.δ_μ_assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simpa only [Functor.comp_obj, Functor.flip_obj_obj, curriedTensor_obj_obj,
    Category.comp_id] using hL'

private theorem sourceShift_comparison_reindex (K M : DerivedCategory C)
    (p q : ℤ) (hp : -p = q) :
    letI := exactClosedDerivedMonoidal F
    F.mapDerivedCategory.map (((siteHomSourceShift K p) ≪≫
        Functor.isoWhiskerLeft (ihom K)
          (eqToIso (congrArg (shiftFunctor (DerivedCategory C)) hp))).hom.app M) ≫
        (F.mapDerivedCategory.commShiftIso q).hom.app ((ihom K).obj M) ≫
        (closedComparison F.mapDerivedCategory K M)⟦q⟧' =
      closedComparison F.mapDerivedCategory (K⟦p⟧) M ≫
        (pre ((F.mapDerivedCategory.commShiftIso p).inv.app K)).app
          (F.mapDerivedCategory.obj M) ≫
        (((siteHomSourceShift (F.mapDerivedCategory.obj K) p) ≪≫
          Functor.isoWhiskerLeft (ihom (F.mapDerivedCategory.obj K))
            (eqToIso (congrArg (shiftFunctor (DerivedCategory D)) hp))).hom.app
              (F.mapDerivedCategory.obj M)) := by
  subst q
  letI := exactClosedDerivedMonoidal F
  simpa [closedComparison] using
    sourceShift_comparison F.mapDerivedCategory K M p
      (fun X ↦ tensor_interchange F K X p)

private theorem oppositeSourceShift_comparison (K M : DerivedCategory C) (n : ℤ) :
    letI := exactClosedDerivedMonoidal F
    F.mapDerivedCategory.map ((siteHomOppositeSourceShift K n).hom.app M) ≫
        (F.mapDerivedCategory.commShiftIso n).hom.app ((ihom K).obj M) ≫
        (closedComparison F.mapDerivedCategory K M)⟦n⟧' =
      closedComparison F.mapDerivedCategory (K⟦-n⟧) M ≫
        (pre ((F.mapDerivedCategory.commShiftIso (-n)).inv.app K)).app
          (F.mapDerivedCategory.obj M) ≫
        (siteHomOppositeSourceShift (F.mapDerivedCategory.obj K) n).hom.app
          (F.mapDerivedCategory.obj M) := by
  letI := exactClosedDerivedMonoidal F
  simpa only [siteHomOppositeSourceShift] using
    sourceShift_comparison_reindex F K M (-n) n (neg_neg n)

end Derived

/-- The evaluation transpose of an exact derived monoidal functor respects the signed
contravariant source shifts. This asserts a shift square only, not exactness or thick closure.
Source: Stacks Project, Tags 08J9 and 08JC; steps 2--4 of the site comparison argument
(blueprint: lem-sf-exact-derived-hom-comparison-shift).

Proof: choose a K-injective representative I of M and a K-injective replacement
q:FI -> J. The ordinary map F Hom(E,I) -> Hom(FE,FI) -> Hom(FE,J) is natural in E.
Use a K-flat resolution of E and a K-flat resolution of Hom(E,I). On each tensor
summand, uncurrying this composite is q after pulled-back evaluation. Thus its
localization is the stated canonical closedComparison, for the transported derived
monoidal structure. For E[m], signed reindexing multiplies degree k by (-1)^(m*k).
Ordinary pullback preserves this scalar and postcomposition with q preserves it,
so both routes around the raw shift square agree on every Hom projection. Localize
and use the K-flat representative comparison to identify the raw shifts with the
adjoint mates siteHomOppositeSourceShift. Multiply both rows by the same scalar
(-1)^(n*(n+1)/2). The two supplied normalizations therefore give precisely the
CommShift square. No preservation of K-injectives by F is used. -/
theorem exactDerivedHomComparison_shift
    {C : Type c} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {D : Type d} [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D]
    [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal] (M : DerivedCategory C)
    (sC : (MonoidalClosed.internalHom.flip.obj M).CommShift ℤ)
    (sD : (MonoidalClosed.internalHom.flip.obj (F.mapDerivedCategory.obj M)).CommShift ℤ)
    (hC : letI := sC; ∀ (K : DerivedCategory C) (n : ℤ),
      ((MonoidalClosed.internalHom.flip.obj M).commShiftIso n).hom.app (op K) =
        (n * (n + 1) / 2).negOnePow • (siteHomOppositeSourceShift K n).hom.app M)
    (hD : letI := sD; ∀ (K : DerivedCategory D) (n : ℤ),
      ((MonoidalClosed.internalHom.flip.obj (F.mapDerivedCategory.obj M)).commShiftIso n).hom.app
          (op K) = (n * (n + 1) / 2).negOnePow •
            (siteHomOppositeSourceShift K n).hom.app (F.mapDerivedCategory.obj M)) :
    letI := sC
    letI := sD
    letI := exactClosedDerivedMonoidal F
    ∀ β : MonoidalClosed.internalHom.flip.obj M ⋙ F.mapDerivedCategory ⟶
      F.mapDerivedCategory.op ⋙ MonoidalClosed.internalHom.flip.obj (F.mapDerivedCategory.obj M),
      (∀ K, β.app (op K) = closedComparison F.mapDerivedCategory K M) →
        NatTrans.CommShift β ℤ := by
  -- Use the canonical tensor comparison and its mates, then the common signed scalar.
  letI := sC
  letI := sD
  letI := exactClosedDerivedMonoidal F
  intro β hβ
  constructor
  intro n
  apply NatTrans.ext
  funext K
  cases K with
  | op K =>
    have hB : ((MonoidalClosed.internalHom.flip.obj M ⋙
        F.mapDerivedCategory).commShiftIso n).hom.app (op K) = (n * (n + 1) / 2).negOnePow •
          (F.mapDerivedCategory.map ((siteHomOppositeSourceShift K n).hom.app M) ≫
            (F.mapDerivedCategory.commShiftIso n).hom.app ((ihom K).obj M)) := by
      rw [Functor.commShiftIso_comp_hom_app, hC]
      simp only [Functor.map_units_smul, Linear.units_smul_comp]
      rfl
    have hE : ((F.mapDerivedCategory.op ⋙ MonoidalClosed.internalHom.flip.obj
        (F.mapDerivedCategory.obj M)).commShiftIso n).hom.app (op K) =
        (n * (n + 1) / 2).negOnePow •
          ((pre ((F.mapDerivedCategory.commShiftIso (-n)).inv.app K)).app
              (F.mapDerivedCategory.obj M) ≫
            (siteHomOppositeSourceShift (F.mapDerivedCategory.obj K) n).hom.app
              (F.mapDerivedCategory.obj M)) := by
      rw [Functor.commShiftIso_comp_hom_app]
      have hFop : (F.mapDerivedCategory.op.commShiftIso n).hom.app (op K) =
          ((F.mapDerivedCategory.commShiftIso (-n)).inv.app K).op := by
        rw [Functor.op_commShiftIso_hom_app F.mapDerivedCategory (op K) n (-n)
          (add_neg_cancel n)]
        change (F.mapDerivedCategory.map (𝟙 _)).op ≫ _ ≫ 𝟙 _ = _
        rw [Functor.map_id, op_id, Category.id_comp, Category.comp_id]
      rw [hFop, hD]
      simp only [Linear.comp_units_smul]
      rfl
    change _ ≫ (β.app (op K))⟦n⟧' = β.app (op (K⟦-n⟧)) ≫ _
    rw [hB, hE, hβ, hβ]
    simp only [Linear.units_smul_comp, Linear.comp_units_smul, Category.assoc]
    exact congrArg (fun f ↦ (n * (n + 1) / 2).negOnePow • f)
      (oppositeSourceShift_comparison F K M n)

end CategoryTheory.Functor
