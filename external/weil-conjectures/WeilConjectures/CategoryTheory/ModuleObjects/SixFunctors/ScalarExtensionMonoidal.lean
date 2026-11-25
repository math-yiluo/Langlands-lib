/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import all WeilConjectures.CategoryTheory.ModuleObjects.SixFunctors.ScalarTensorCancellation

/-! # Monoidal extension of scalars of internal modules

Source: Stacks Tag 07A4, tensor products and change of rings.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe v u

open CategoryTheory MonoidalCategory MonObj Limits BraidedCategory

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ]

omit [MonObj R] [IsCommMonObj R] [IsMonHom φ] in
private lemma restrictionTensor_balanced (M N : Mod C S) :
    ((β_ M.X R).hom ≫ φ ▷ M.X ≫ γ[S,M.X]) ▷ N.X ≫ tensorObjπ M N =
      ((α_ M.X R N.X).hom ≫ M.X ◁ (φ ▷ N.X ≫ γ[S,N.X])) ≫ tensorObjπ M N := by
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  slice_lhs 1 2 =>
    rw [← comp_whiskerRight, ← braiding_naturality_right, comp_whiskerRight]
  slice_lhs 2 3 => rw [← comp_whiskerRight]
  rw [tensorObjπ_condition, Category.assoc, associator_naturality_middle_assoc]

set_option backward.isDefEq.respectTransparency false in
private def restrictionTensor (M N : Mod C S) :
    (comap φ).obj M ⊗ (comap φ).obj N ⟶ (comap φ).obj (M ⊗ N) :=
  Hom.mk' (tensorObjDesc _ _ (tensorObjπ M N) (restrictionTensor_balanced φ M N)) (by
    rw [← cancel_epi (R ◁ tensorObjπ ((comap φ).obj M) ((comap φ).obj N)),
      whiskerLeft_tensorπ_smul_assoc, tensorObjπ_tensorObjDesc]
    erw [← whiskerLeft_comp_assoc, tensorObjπ_tensorObjDesc]
    change (α_ R M.X N.X).inv ≫ (φ ▷ M.X ≫ γ[S,M.X]) ▷ N.X ≫ tensorObjπ M N =
      R ◁ tensorObjπ M N ≫ φ ▷ (M ⊗ N).X ≫ γ[S,(M ⊗ N).X]
    rw [whisker_exchange_assoc, whiskerLeft_tensorπ_smul,
      associator_inv_naturality_left_assoc, comp_whiskerRight, Category.assoc])

@[reassoc]
private lemma restrictionTensor_π (M N : Mod C S) :
    tensorObjπ ((comap φ).obj M) ((comap φ).obj N) ≫ (restrictionTensor φ M N).hom =
      tensorObjπ M N := tensorObjπ_tensorObjDesc _ _ _ _

private def restrictionUnit : regular R ⟶ (comap φ).obj (regular S) :=
  Hom.mk' φ (by
    change μ[R] ≫ φ = R ◁ φ ≫ φ ▷ S ≫ μ[S]
    rw [IsMonHom.mul_hom, tensorHom_def', Category.assoc])

private lemma tensorUnit_left (M : Mod C R) :
    tensorObjπ (regular R) M ≫ (λ_ M).hom.hom = γ[R,M.X] := by
  change tensorObjπ (regular R) M ≫
    (Bimod.whiskerRight (toBimodRegularIso (R := R)).hom ((toBimod R).obj M)).hom ≫
      Bimod.LeftUnitorBimod.hom ((toBimod R).obj M) = _
  dsimp only [tensorObjπ]
  rw [Bimod.whiskerRight_hom]
  erw [ι_colimMap_assoc]
  simp only [parallelPairHom_app_one]
  erw [toBimodRegularIso_hom_hom, id_whiskerRight, Category.id_comp]
  exact coequalizer.π_desc _ _

private lemma tensorUnit_right (M : Mod C R) :
    tensorObjπ M (regular R) ≫ (ρ_ M).hom.hom = (β_ M.X R).hom ≫ γ[R,M.X] := by
  change tensorObjπ M (regular R) ≫
    (Bimod.whiskerLeft ((toBimod R).obj M) (toBimodRegularIso (R := R)).hom).hom ≫
      Bimod.RightUnitorBimod.hom ((toBimod R).obj M) = _
  dsimp only [tensorObjπ]
  rw [Bimod.whiskerLeft_hom]
  erw [ι_colimMap_assoc]
  simp only [parallelPairHom_app_one]
  erw [toBimodRegularIso_hom_hom, whiskerLeft_id, Category.id_comp]
  exact coequalizer.π_desc _ _

set_option backward.isDefEq.respectTransparency false in
@[instance_reducible]
private def restrictionLaxMonoidal : (comap φ : Mod C S ⥤ Mod C R).LaxMonoidal where
  ε := restrictionUnit φ
  «μ» M N := restrictionTensor φ M N
  μ_natural_left f N := by
    apply hom_ext
    rw [← cancel_epi (tensorObjπ ((comap φ).obj _) ((comap φ).obj N))]
    change tensorObjπ _ _ ≫ ((comap φ).map f ▷ _).hom ≫ _ =
      tensorObjπ _ _ ≫ (restrictionTensor φ _ N).hom ≫ (f ▷ N).hom
    erw [tensorObjπ_whiskerRight_assoc, restrictionTensor_π,
      restrictionTensor_π_assoc, tensorObjπ_whiskerRight]
    rfl
  μ_natural_right M f := by
    apply hom_ext
    rw [← cancel_epi (tensorObjπ ((comap φ).obj M) ((comap φ).obj _))]
    change tensorObjπ _ _ ≫ (_ ◁ (comap φ).map f).hom ≫ _ =
      tensorObjπ _ _ ≫ (restrictionTensor φ M _).hom ≫ (M ◁ f).hom
    erw [tensorObjπ_whiskerLeft_assoc, restrictionTensor_π,
      restrictionTensor_π_assoc, tensorObjπ_whiskerLeft]
    rfl
  associativity M N P := by
    apply hom_ext
    rw [← cancel_epi (tensorObjπ ((comap φ).obj M ⊗ (comap φ).obj N) ((comap φ).obj P))]
    rw [← cancel_epi (tensorObjπ ((comap φ).obj M) ((comap φ).obj N) ▷ ((comap φ).obj P).X)]
    simp only [comp_hom']
    erw [tensorObjπ_whiskerRight_assoc]
    erw [← comp_whiskerRight_assoc, restrictionTensor_π]
    erw [restrictionTensor_π_assoc, tensorObjπ_associator_hom]
    erw [tensorObjπ_associator_hom_assoc, tensorObjπ_whiskerLeft_assoc]
    erw [← whiskerLeft_comp_assoc, restrictionTensor_π]
    erw [restrictionTensor_π]
    rfl
  left_unitality M := by
    apply hom_ext
    rw [← cancel_epi (tensorObjπ (regular R) ((comap φ).obj M))]
    simp only [comp_hom']
    erw [tensorObjπ_whiskerRight_assoc, restrictionTensor_π_assoc, tensorUnit_left,
      tensorUnit_left]
    rfl
  right_unitality M := by
    apply hom_ext
    rw [← cancel_epi (tensorObjπ ((comap φ).obj M) (regular R))]
    simp only [comp_hom']
    erw [tensorObjπ_whiskerLeft_assoc, restrictionTensor_π_assoc, tensorUnit_right,
      tensorUnit_right]
    change (β_ M.X R).hom ≫ φ ▷ M.X ≫ γ[S,M.X] =
      M.X ◁ φ ≫ (β_ M.X S).hom ≫ γ[S,M.X]
    rw [braiding_naturality_right_assoc]

set_option backward.isDefEq.respectTransparency false in
private def scalarBimod : Bimod (Mon.mk R) (Mon.mk R) :=
  { toBimodObj R ((comap φ).obj (regular S)) with
    actRight := S ◁ φ ≫ μ[S]
    actRight_one := (Bimod.ofMonHom φ).actRight_one
    right_assoc := (Bimod.ofMonHom φ).right_assoc
    middle_assoc := by
      change (φ ▷ S ≫ μ[S]) ▷ R ≫ (S ◁ φ ≫ μ[S]) =
        (α_ R S R).hom ≫ R ◁ (S ◁ φ ≫ μ[S]) ≫ (φ ▷ S ≫ μ[S])
      rw [← restrictedRegular_rightAction φ]
      exact (toBimodObj R ((comap φ).obj (regular S))).middle_assoc }

set_option backward.isDefEq.respectTransparency false in
private lemma scalarBimod_tensor_action (M : Mod C R) :
    ((scalarBimod φ).tensorBimod (toBimodObj R M)).actLeft =
      φ ▷ (extendScalarsObj φ M).X ≫ γ[S,(extendScalarsObj φ M).X] := by
  apply (cancel_epi (R ◁ extendπ φ M)).1
  calc
    _ = (α_ R S M.X).inv ≫ (φ ▷ S ≫ μ[S]) ▷ M.X ≫ extendπ φ M :=
      Bimod.TensorBimod.whiskerLeft_π_actLeft (scalarBimod φ) (toBimodObj R M)
    _ = _ := ?_
  rw [whisker_exchange_assoc, whiskerLeft_extendπ_smul,
    associator_inv_naturality_left_assoc, comp_whiskerRight, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private lemma extended_right_action (M : Mod C R) :
    (extendScalarsBimod φ M).actRight =
      (restrictRight φ (toBimodObj S ((extendScalars φ).obj M))).actRight := by
  have h : (scalarBimod φ).IsSymmetric := (restrictedRegular_rightAction φ).symm
  have ht := h.tensorBimod (Bimod.isSymmetric_toBimodObj M)
  change (extendScalarsBimod φ M).actRight =
    (β_ (extendScalarsObj φ M).X R).hom ≫
      ((scalarBimod φ).tensorBimod (toBimodObj R M)).actLeft at ht
  rw [scalarBimod_tensor_action] at ht
  rw [ht]
  change (β_ (extendScalarsObj φ M).X R).hom ≫
      φ ▷ (extendScalarsObj φ M).X ≫ γ[S,(extendScalarsObj φ M).X] =
    (extendScalarsObj φ M).X ◁ φ ≫ (β_ (extendScalarsObj φ M).X S).hom ≫
      γ[S,(extendScalarsObj φ M).X]
  rw [braiding_naturality_right_assoc]

private def extendedRestrictRightIso (M : Mod C R) :
    extendScalarsBimod φ M ≅ restrictRight φ (toBimodObj S ((extendScalars φ).obj M)) :=
  Bimod.isoOfIso (Iso.refl _) (by simp; rfl) (by
    simp only [Iso.refl_hom, Category.comp_id, id_whiskerRight, Category.id_comp]
    exact extended_right_action φ M)

private def bimodTensorLeft {A B D : Mon C} (P : Bimod A B) :
    Bimod B D ⥤ Bimod A D where
  obj N := P.tensorBimod N
  map f := Bimod.whiskerLeft P f
  map_id _N := Bimod.whiskerLeft_id_bimod
  map_comp f g := Bimod.whiskerLeft_comp_bimod P f g

private def tensorComparisonBimodIso (M N : Mod C R) :
    (toBimodObj S ((extendScalars φ).obj M)).tensorBimod (extendScalarsBimod φ N) ≅
      extendScalarsBimod φ (M ⊗ N) :=
  cancellationBimodIso φ N (toBimodObj S ((extendScalars φ).obj M)) ≪≫
    (bimodTensorRight (toBimodObj R N)).mapIso (extendedRestrictRightIso φ M).symm ≪≫
    Bimod.associatorBimod (Bimod.ofMonHom φ) (toBimodObj R M) (toBimodObj R N) ≪≫
    (bimodTensorLeft (Bimod.ofMonHom φ)).mapIso (toBimodTensorIso M N).symm

set_option backward.isDefEq.respectTransparency false in
private def tensorComparisonIso (M N : Mod C R) :
    (extendScalars φ).obj M ⊗ (extendScalars φ).obj N ≅ (extendScalars φ).obj (M ⊗ N) :=
  isoMk ((bimodForget (Mon.mk S) (Mon.mk R)).mapIso (tensorComparisonBimodIso φ M N))
    (tensorComparisonBimodIso φ M N).hom.left_act_hom

private def unitComparisonBimodIso :
    extendScalarsBimod φ (regular R) ≅ Bimod.ofMonHom φ :=
  (bimodTensorLeft (Bimod.ofMonHom φ)).mapIso toBimodRegularIso ≪≫
    Bimod.rightUnitorBimod (Bimod.ofMonHom φ)

set_option backward.isDefEq.respectTransparency false in
private def unitComparisonIso : (extendScalars φ).obj (regular R) ≅ regular S :=
  isoMk ((bimodForget (Mon.mk S) (Mon.mk R)).mapIso (unitComparisonBimodIso φ))
    (unitComparisonBimodIso φ).hom.left_act_hom

omit [IsCommMonObj S] in
set_option backward.isDefEq.respectTransparency false in
private lemma cancellationBimodIso_π (M : Mod C R) {A : Mon C}
    (P : Bimod A (Mon.mk S)) :
    P.X ◁ extendπ φ M ≫ coequalizer.π _ _ ≫ (cancellationBimodIso φ M P).hom.hom =
      (α_ P.X S M.X).inv ≫ P.actRight ▷ M.X ≫ coequalizer.π _ _ := by
  dsimp only [cancellationBimodIso, Iso.trans_hom, Iso.symm_hom,
    Bimod.comp_hom', Functor.mapIso_hom, Bimod.associatorBimod, Bimod.isoOfIso,
    Bimod.AssociatorBimod.inv]
  erw [coequalizer.π_desc_assoc]
  dsimp only [Bimod.AssociatorBimod.invAux]
  simp only [Category.assoc]
  slice_lhs 1 3 => erw [id_tensor_π_preserves_coequalizer_inv_desc]
  dsimp only [bimodTensorRight, Bimod.whiskerRight]
  simp only [Category.assoc]
  erw [ι_colimMap]
  simp only [parallelPairHom_app_one]
  rw [← comp_whiskerRight_assoc]
  dsimp only [restrictRightUnitIso, Bimod.isoOfIso, Bimod.RightUnitorBimod.hom]
  erw [coequalizer.π_desc]
  rfl

omit [IsCommMonObj S] in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private lemma cancellationBimodIso_unit (M : Mod C R) {A : Mon C}
    (P : Bimod A (Mon.mk S)) :
    P.X ◁ extendUnitHom φ M ≫ coequalizer.π _ _ ≫
        (cancellationBimodIso φ M P).hom.hom = coequalizer.π _ _ := by
  dsimp only [extendUnitHom]
  rw [whiskerLeft_comp_assoc, whiskerLeft_comp_assoc, cancellationBimodIso_π]
  rw [associator_inv_naturality_middle_assoc,
    whiskerLeft_leftUnitor_inv_associator_inv_assoc]
  slice_lhs 2 3 => rw [← comp_whiskerRight, P.actRight_one]
  rw [← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight, Category.id_comp]

omit [SymmetricCategory C] in
set_option backward.isDefEq.respectTransparency false in
private lemma bimodAssociator_π {A B D E : Mon C}
    (P : Bimod A B) (Q : Bimod B D) (T : Bimod D E) :
    coequalizer.π _ _ ▷ T.X ≫ coequalizer.π _ _ ≫
        (Bimod.associatorBimod P Q T).hom.hom =
      (α_ P.X Q.X T.X).hom ≫ P.X ◁ coequalizer.π _ _ ≫ coequalizer.π _ _ := by
  dsimp only [Bimod.associatorBimod, Bimod.isoOfIso, Bimod.AssociatorBimod.hom,
    Bimod.AssociatorBimod.homAux]
  erw [coequalizer.π_desc]
  exact π_tensor_id_preserves_coequalizer_inv_desc _ _ _ _

set_option backward.isDefEq.respectTransparency false in
private lemma tensorComparison_unit (M N : Mod C R) :
    (extendUnitHom φ M ⊗ₘ extendUnitHom φ N) ≫
        tensorObjπ ((extendScalars φ).obj M) ((extendScalars φ).obj N) ≫
          (tensorComparisonIso φ M N).hom.hom =
      tensorObjπ M N ≫ extendUnitHom φ (M ⊗ N) := by
  change (extendUnitHom φ M ⊗ₘ extendUnitHom φ N) ≫
    tensorObjπ ((extendScalars φ).obj M) ((extendScalars φ).obj N) ≫
      (tensorComparisonBimodIso φ M N).hom.hom = _
  rw [MonoidalCategory.tensorHom_def (extendUnitHom φ M) (extendUnitHom φ N)]
  dsimp only [tensorComparisonBimodIso, Iso.trans_hom, Bimod.comp_hom']
  simp only [Category.assoc]
  erw [reassoc_of% cancellationBimodIso_unit φ N
    (toBimodObj S ((extendScalars φ).obj M))]
  dsimp only [bimodTensorRight, Functor.mapIso_hom, Iso.symm_hom, Bimod.whiskerRight]
  erw [ι_colimMap_assoc]
  simp only [parallelPairHom_app_one]
  change extendUnitHom φ M ▷ N.X ≫ (𝟙 _ ▷ N.X) ≫ coequalizer.π _ _ ≫ _ = _
  rw [id_whiskerRight, Category.id_comp]
  dsimp only [extendUnitHom]
  simp only [comp_whiskerRight, Category.assoc]
  erw [reassoc_of% bimodAssociator_π
    (Bimod.ofMonHom φ) (toBimodObj R M) (toBimodObj R N)]
  dsimp only [bimodTensorLeft, Functor.mapIso_hom, Iso.symm_hom, Bimod.whiskerLeft]
  erw [ι_colimMap]
  simp only [parallelPairHom_app_one]
  erw [toBimodTensorIso_inv_hom, whiskerLeft_id, Category.id_comp]
  change (λ_ M.X).inv ▷ N.X ≫ η[S] ▷ M.X ▷ N.X ≫
    (α_ S M.X N.X).hom ≫ S ◁ tensorObjπ M N ≫ extendπ φ (M ⊗ N) = _
  rw [associator_naturality_left_assoc, ← leftUnitor_tensor_inv_assoc,
    ← whisker_exchange_assoc, ← leftUnitor_inv_naturality_assoc]

omit [IsCommMonObj S] in
set_option backward.isDefEq.respectTransparency false in
private lemma unitComparison_π :
    extendπ φ (regular R) ≫ (unitComparisonIso φ).hom.hom = S ◁ φ ≫ μ[S] := by
  dsimp only [unitComparisonIso, isoMk, unitComparisonBimodIso, Iso.trans_hom,
    Bimod.comp_hom', Functor.mapIso_hom, bimodForget, bimodTensorLeft, homMk,
    Bimod.whiskerLeft]
  erw [ι_colimMap_assoc]
  simp only [parallelPairHom_app_one]
  erw [toBimodRegularIso_hom_hom, whiskerLeft_id, Category.id_comp]
  dsimp only [Bimod.rightUnitorBimod, Bimod.isoOfIso, Bimod.RightUnitorBimod.hom]
  erw [coequalizer.π_desc]
  rfl

omit [IsCommMonObj S] in
private lemma unitComparison_unit :
    extendUnitHom φ (regular R) ≫ (unitComparisonIso φ).hom.hom = φ := by
  dsimp only [extendUnitHom]
  rw [Category.assoc, Category.assoc, unitComparison_π]
  exact MonObj.leftUnitor_inv_one_whiskerRight_whiskerLeft_mul φ

omit [IsCommMonObj S] in
private lemma scalarAdj_homEquiv :
    (extendRestrictAdjunction φ).homEquiv = extendHomEquiv φ := by
  exact Adjunction.mkOfHomEquiv_homEquiv _

omit [IsCommMonObj S] in
private lemma scalarAdj_unit (M : Mod C R) :
    (extendRestrictAdjunction φ).unit.app M = extendUnit φ M := by
  rw [← Adjunction.homEquiv_id, scalarAdj_homEquiv]
  change extendUnit φ M ≫ (comap φ).map (𝟙 _) = _
  simp

@[instance_reducible]
private def canonicalOplax : (extendScalars φ).OplaxMonoidal :=
  letI := restrictionLaxMonoidal φ
  (extendRestrictAdjunction φ).leftAdjointOplaxMonoidal

@[reassoc]
private lemma canonicalOplax_normalized (M N : Mod C R) :
    tensorObjπ M N ≫ extendUnitHom φ (M ⊗ N) ≫
        ((canonicalOplax φ).δ M N).hom =
      (extendUnitHom φ M ⊗ₘ extendUnitHom φ N) ≫
        tensorObjπ ((extendScalars φ).obj M) ((extendScalars φ).obj N) := by
  dsimp only [Functor.OplaxMonoidal.δ, Functor.OplaxMonoidal.η, canonicalOplax,
    Adjunction.leftAdjointOplaxMonoidal]
  rw [scalarAdj_homEquiv, scalarAdj_unit, scalarAdj_unit]
  change tensorObjπ M N ≫ extendUnitHom φ (M ⊗ N) ≫
    (extendHom φ ((extendUnit φ M ⊗ₘ extendUnit φ N) ≫
      restrictionTensor φ _ _)).hom = _
  rw [extendUnitHom_extendHom]
  rw [MonoidalCategory.tensorHom_def (extendUnit φ M) (extendUnit φ N)]
  simp only [comp_hom', Category.assoc]
  erw [tensorObjπ_whiskerRight_assoc, tensorObjπ_whiskerLeft_assoc,
    restrictionTensor_π]
  rw [MonoidalCategory.tensorHom_def (extendUnitHom φ M) (extendUnitHom φ N)]
  simp only [Category.assoc]
  rfl

/-- Extension of scalars of internal modules has a scalar-unit normalized strong
monoidal structure. Source: Stacks, sites-modules.tex, lemma-tensor-product-pullback;
Tag 07A4, balanced tensors and change of rings.
(blueprint: lem-sfb-internal-extension-monoidal).
Proof: restriction is lax monoidal by the balanced tensor universal property. Its
left adjoint is therefore oplax monoidal. Bimodule associativity and the regular
bimodule unit laws give inverse isomorphisms for these oplax maps; they agree by
precomposition with scalar units. The adjunction makes this precomposition injective.
-/
theorem exists_extendScalarsMonoidal :
    ∃ m : (extendScalars φ).Monoidal, ∀ M N : Mod C R,
      tensorObjπ M N ≫ (extendUnit φ (M ⊗ N)).hom ≫
          (m.toOplaxMonoidal.δ M N).hom =
        ((extendUnit φ M).hom ⊗ₘ (extendUnit φ N).hom) ≫
          tensorObjπ ((extendScalars φ).obj M) ((extendScalars φ).obj N) := by
  let := canonicalOplax φ
  have hη : (canonicalOplax φ).η = (unitComparisonIso φ).hom := by
    apply (extendHomEquiv φ (regular R) (regular S)).injective
    apply hom_ext
    dsimp only [Functor.OplaxMonoidal.δ, Functor.OplaxMonoidal.η, canonicalOplax,
      Adjunction.leftAdjointOplaxMonoidal]
    rw [scalarAdj_homEquiv]
    change extendUnitHom φ (regular R) ≫ (extendHom φ (restrictionUnit φ)).hom =
      extendUnitHom φ (regular R) ≫ (unitComparisonIso φ).hom.hom
    rw [extendUnitHom_extendHom, unitComparison_unit]
    rfl
  have hδ (M N : Mod C R) :
      (canonicalOplax φ).δ M N = (tensorComparisonIso φ M N).inv := by
    apply (cancel_mono (tensorComparisonIso φ M N).hom).1
    rw [Iso.inv_hom_id]
    apply (extendHomEquiv φ (M ⊗ N) _).injective
    apply hom_ext
    change extendUnitHom φ (M ⊗ N) ≫ ((canonicalOplax φ).δ M N).hom ≫
      (tensorComparisonIso φ M N).hom.hom = extendUnitHom φ (M ⊗ N) ≫ 𝟙 _
    apply (cancel_epi (tensorObjπ M N)).1
    erw [canonicalOplax_normalized_assoc, tensorComparison_unit, Category.comp_id]
  have : IsIso (Functor.OplaxMonoidal.η (extendScalars φ)) := by
    change IsIso ((canonicalOplax φ).η)
    rw [hη]
    infer_instance
  have (M N : Mod C R) : IsIso (Functor.OplaxMonoidal.δ (extendScalars φ) M N) := by
    change IsIso ((canonicalOplax φ).δ M N)
    rw [hδ]
    infer_instance
  let m := Functor.Monoidal.ofOplaxMonoidal (extendScalars φ)
  refine ⟨m, ?_⟩
  intro M N
  exact canonicalOplax_normalized φ M N

end CategoryTheory.Mod
