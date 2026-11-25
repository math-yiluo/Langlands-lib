/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement

/-!
# Cancellation of opposite canonical derived tensor symmetries

Source: Stacks Project, Tag 06YU, the signed symmetry on total tensor complexes.
-/

@[expose] public section

universe w v v₁ v₂ u₁ u₂ u' u

open CategoryTheory Limits MonoidalCategory

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize in
private theorem cochain_braiding_involutive
    {C : Type u'} [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C]
    [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
    [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
    [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    (hs : ∀ U V : C, (β_ U V).hom ≫ (β_ V U).hom = 𝟙 _)
    (K M : CochainComplex C ℤ) :
    (CochainComplex.Monoidal.braiding K M).hom ≫
      (CochainComplex.Monoidal.braiding M K).hom = 𝟙 _ := by
  ext n
  apply HomologicalComplex.mapBifunctor.hom_ext (K₁ := K) (K₂ := M)
    (F := curriedTensor C)
  intro p q h
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f]
  rw [← Category.assoc,
    CochainComplex.Monoidal.ι_braiding_hom (K := K) (L := M) p q n h]
  rw [Preadditive.zsmul_comp, Category.assoc,
    CochainComplex.Monoidal.ι_braiding_hom (K := M) (L := K) q p n
      (by rw [add_comm]; exact h), Preadditive.comp_zsmul,
    ← Category.assoc, hs]
  simp only [smul_smul, mul_comm p q, Int.units_coe_mul_self, one_smul,
    Category.id_comp, curriedTensor_obj_obj]
  exact (Category.comp_id _).symm

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize in
private theorem homotopy_braiding_swap
    {C : Type u'} [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C]
    [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
    [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
    [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    (hs : ∀ U V : C, (β_ U V).hom ≫ (β_ V U).hom = 𝟙 _)
    (K M : HomotopyCategory C (.up ℤ)) : (β_ K M).hom = (β_ M K).inv := by
  apply Iso.inv_ext'
  obtain ⟨K, rfl⟩ := K.quotient_obj_surjective
  obtain ⟨M, rfl⟩ := M.quotient_obj_surjective
  change (HomotopyCategory.quotient C (.up ℤ)).map
      (CochainComplex.Monoidal.braiding M K).hom ≫
    (HomotopyCategory.quotient C (.up ℤ)).map
      (CochainComplex.Monoidal.braiding K M).hom = 𝟙 _
  rw [← Functor.map_comp, cochain_braiding_involutive hs]
  exact (HomotopyCategory.quotient C (.up ℤ)).map_id _

private def swapInvolutive {D : Type u₁} [Category.{v₁} D]
    {P : D ⥤ D ⥤ D} (s : P ≅ P.flip) : Prop :=
  ∀ K M, (s.hom.app K).app M ≫ (s.hom.app M).app K = 𝟙 _

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize in
private theorem canonicalBraiding_involutive
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [MonoidalCategory C] [BraidedCategory C]
    (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] [W.ContainsIdentities] [L.HasDerivedMonoidalCategory W]
    (hs : ∀ X Y : C, (β_ X Y).hom = (β_ Y X).inv)
    : swapInvolutive (DerivedMonoidal.canonicalBraidingNatIso L W) := by
  intro K M
  have h : DerivedMonoidal.braidingNatTrans L W =
      DerivedMonoidal.braidingInvNatTrans L W := by
    apply (DerivedMonoidal.bifunctor L W).leftDerived₂_ext
      (DerivedMonoidal.counit L W) W W
    ext X Y
    change ((DerivedMonoidal.braidingNatTrans L W).app
        ((toDerivedMonoidal L W).obj X)).app ((toDerivedMonoidal L W).obj Y) ≫
        ((DerivedMonoidal.counit L W).app X).app Y =
      ((DerivedMonoidal.braidingInvNatTrans L W).app
        ((toDerivedMonoidal L W).obj X)).app ((toDerivedMonoidal L W).obj Y) ≫
        ((DerivedMonoidal.counit L W).app X).app Y
    rw [DerivedMonoidal.braidingNatTrans_fac, DerivedMonoidal.braidingInvNatTrans_fac, hs]
  change ((DerivedMonoidal.braidingNatTrans L W).app M).app K ≫
    ((DerivedMonoidal.braidingNatTrans L W).app K).app M = 𝟙 _
  conv_lhs => rhs; rw [h]
  exact congr_app
    (congr_app (DerivedMonoidal.braidingNatTrans_comp_braidingInvNatTrans L W) K) M

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize in
private theorem canonicalTensorSymmetry_involutive
    (C : Type u') [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [HasDerivedCategory.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [BraidedCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (hs : ∀ U V : C, (β_ U V).hom ≫ (β_ V U).hom = 𝟙 _) :
    swapInvolutive (DerivedCategory.canonicalTensorSymmetry C) := by
  let : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink C
  have : ∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂ := inferInstance
  have : ∀ X₁, PreservesColimit (Functor.empty.{0} C)
      ((curriedTensor C).obj X₁) := inferInstance
  have : ∀ X₂, PreservesColimit (Functor.empty.{0} C)
      ((curriedTensor C).flip.obj X₂) := inferInstance
  have : ∀ (X₁ X₂ X₃ : GradedObject ℤ C),
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := inferInstance
  have : ∀ (X₁ X₂ X₃ : GradedObject ℤ C),
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := inferInstance
  have : ∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := inferInstance
  rw [DerivedCategory.canonicalTensorSymmetry_eq]
  exact canonicalBraiding_involutive DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) (homotopy_braiding_swap hs)

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize in
private theorem etaleTensorSymmetry_involutive
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : AlgebraicGeometry.Scheme.{u}) :
    swapInvolutive (AlgebraicGeometry.Etale.derivedTensorSymmetry A X) := by
  unfold AlgebraicGeometry.Etale.derivedTensorSymmetry
  exact canonicalTensorSymmetry_involutive (Sheaf X.smallEtaleTopology A)
    (fun U V ↦ SymmetricCategory.symmetry U V)

namespace AlgebraicGeometry.Etale

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize in
/-- Opposite canonical signed swaps cancel.
Source: Stacks Project, Tag 06YU, definition-derived-tor and its signed tensor symmetry
(blueprint: lem-amb-derived-tensor-symmetry-involutive).

Proof: on a cochain tensor summand in bidegree `(p,q)`, the two swaps multiply by
`(-1)^(pq+qp) = 1`, and the two coefficient-category braidings compose to identity.
The universal property of the total tensor coproduct proves the cochain identity.
Apply the homotopy quotient functor to obtain the homotopy-category identity.
Consequently the counits `DerivedMonoidal.braidingCounit` and `braidingInvCounit`
coincide: their final ordinary braidings agree. Their left-derived lifts coincide as
well. The existing inverse-law of `DerivedMonoidal.braiding'` now gives the displayed
identity. This concerns the fixed canonical symmetry, with no choice of an isomorphism.
-/
theorem derivedTensorSymmetry_involutive
    (Λ : Type (u + 1)) [CommRing Λ] (X : AlgebraicGeometry.Scheme.{u})
    (K M : DerivedCategoryModule Λ X) :
    ((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) X).hom.app K).app M ≫
      ((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) X).hom.app M).app K = 𝟙 _ := by
  exact etaleTensorSymmetry_involutive (ModuleCat.{u + 1} Λ) X K M

end AlgebraicGeometry.Etale
