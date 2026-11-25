/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars

/-! # Tensor cancellation for extension of scalars of internal modules

Source: Stacks Tag 07A4, the balanced tensor cancellation in change of rings.
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

set_option backward.isDefEq.respectTransparency false in
private def restrictRight {A : Mon C} (P : Bimod A (Mon.mk S)) :
    Bimod A (Mon.mk R) where
  X := P.X
  actLeft := P.actLeft
  actRight := P.X ◁ φ ≫ P.actRight
  one_actLeft := P.one_actLeft
  actRight_one := by
    rw [← whiskerLeft_comp_assoc, IsMonHom.one_hom, P.actRight_one]
  left_assoc := P.left_assoc
  right_assoc := by
    change P.X ◁ μ[R] ≫ P.X ◁ φ ≫ P.actRight =
      (α_ P.X R R).inv ≫ (P.X ◁ φ ≫ P.actRight) ▷ R ≫ P.X ◁ φ ≫ P.actRight
    rw [← whiskerLeft_comp_assoc, IsMonHom.mul_hom, whiskerLeft_comp_assoc,
      P.right_assoc]
    simp only [MonoidalCategory.tensorHom_def, whiskerLeft_comp,
      comp_whiskerRight, Category.assoc]
    rw [associator_inv_naturality_right_assoc, associator_inv_naturality_middle_assoc,
      whisker_exchange_assoc]
  middle_assoc := by
    rw [← whisker_exchange_assoc, P.middle_assoc, whiskerLeft_comp_assoc,
      associator_naturality_right_assoc]

private def bimodForget (A B : Mon C) : Bimod A B ⥤ C where
  obj P := P.X
  map f := f.hom

set_option backward.isDefEq.respectTransparency false in
private def restrictRightUnitIso {A : Mon C} (P : Bimod A (Mon.mk S)) :
    P.tensorBimod (Bimod.ofMonHom φ) ≅ restrictRight φ P :=
  Bimod.isoOfIso
    { hom := Bimod.RightUnitorBimod.hom P
      inv := Bimod.RightUnitorBimod.inv P
      hom_inv_id := Bimod.RightUnitorBimod.hom_inv_id P
      inv_hom_id := Bimod.RightUnitorBimod.inv_hom_id P }
    (Bimod.RightUnitorBimod.hom_left_act_hom' P) (by
      let q := coequalizer.π (P.actRight ▷ (Bimod.ofMonHom φ).X)
        ((α_ P.X S (Bimod.ofMonHom φ).X).hom ≫ P.X ◁ (Bimod.ofMonHom φ).actLeft)
      have : Epi (q ▷ R) := (tensorRight R).map_epi q
      apply (cancel_epi (q ▷ R)).1
      dsimp only [q]
      erw [reassoc_of% Bimod.TensorBimod.π_tensor_id_actRight P (Bimod.ofMonHom φ)]
      change (α_ P.X S R).hom ≫ P.X ◁ (S ◁ φ ≫ μ[S]) ≫
        coequalizer.π _ _ ≫ Bimod.RightUnitorBimod.hom P =
        coequalizer.π _ _ ▷ R ≫ Bimod.RightUnitorBimod.hom P ▷ R ≫
          P.X ◁ φ ≫ P.actRight
      rw [← comp_whiskerRight_assoc]
      dsimp only [Bimod.RightUnitorBimod.hom]
      erw [coequalizer.π_desc]
      rw [whiskerLeft_comp_assoc, P.right_assoc,
        associator_inv_naturality_right_assoc, Iso.hom_inv_id_assoc,
        whisker_exchange_assoc])

private def bimodTensorRight {A B D : Mon C} (N : Bimod B D) :
    Bimod A B ⥤ Bimod A D where
  obj P := P.tensorBimod N
  map f := Bimod.whiskerRight f N
  map_id _P := Bimod.id_whiskerRight_bimod
  map_comp f g := Bimod.comp_whiskerRight_bimod f g N

private def cancellationBimodIso (M : Mod C R) {A : Mon C}
    (P : Bimod A (Mon.mk S)) :
    P.tensorBimod (extendScalarsBimod φ M) ≅
      (restrictRight φ P).tensorBimod (toBimodObj R M) :=
  (Bimod.associatorBimod P (Bimod.ofMonHom φ) (toBimodObj R M)).symm ≪≫
    (bimodTensorRight (toBimodObj R M)).mapIso (restrictRightUnitIso φ P)

omit [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] in
private lemma restricted_right_action (N : Mod C S) :
    (restrictRight φ (toBimodObj S N)).actRight =
      (toBimodObj R ((comap φ).obj N)).actRight := by
  change N.X ◁ φ ≫ (β_ N.X S).hom ≫ γ[S,N.X] =
    (β_ N.X R).hom ≫ φ ▷ N.X ≫ γ[S,N.X]
  rw [braiding_naturality_right_assoc]

set_option backward.isDefEq.respectTransparency false in
private def restrictedTensorIso (M : Mod C R) (N : Mod C S) :
    ((restrictRight φ (toBimodObj S N)).tensorBimod (toBimodObj R M)).X ≅
      ((comap φ).obj N ⊗ M).X where
  hom := coequalizer.desc (tensorObjπ ((comap φ).obj N) M) (by
    rw [restricted_right_action]
    exact tensorObjπ_condition ((comap φ).obj N) M)
  inv := tensorObjDesc ((comap φ).obj N) M (coequalizer.π _ _) (by
    change ((β_ N.X R).hom ≫ φ ▷ N.X ≫ γ[S,N.X]) ▷ M.X ≫ _ = _
    rw [← braiding_naturality_right_assoc]
    exact coequalizer.condition _ _)
  hom_inv_id := by
    apply coequalizer.hom_ext
    erw [coequalizer.π_desc_assoc, tensorObjπ_tensorObjDesc, Category.comp_id]
  inv_hom_id := by
    rw [← cancel_epi (tensorObjπ ((comap φ).obj N) M),
      tensorObjπ_tensorObjDesc_assoc, coequalizer.π_desc, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private def cancellationIso (M : Mod C R) (N : Mod C S) :
    (N ⊗ (extendScalars φ).obj M).X ≅ ((comap φ).obj N ⊗ M).X :=
  (bimodForget (Mon.mk S) (Mon.mk R)).mapIso
    (cancellationBimodIso φ M (toBimodObj S N)) ≪≫ restrictedTensorIso φ M N

set_option backward.isDefEq.respectTransparency false in
private lemma cancellationIso_π (M : Mod C R) (N : Mod C S) :
    N.X ◁ extendπ φ M ≫ tensorObjπ N ((extendScalars φ).obj M) ≫
        (cancellationIso φ M N).hom =
      (α_ N.X S M.X).inv ≫ ((β_ N.X S).hom ≫ γ[S,N.X]) ▷ M.X ≫
        tensorObjπ ((comap φ).obj N) M := by
  dsimp only [cancellationIso, Iso.trans_hom, Functor.mapIso_hom, bimodForget,
    cancellationBimodIso, Iso.symm_hom, Bimod.associatorBimod, Bimod.isoOfIso,
    Bimod.comp_hom', Bimod.AssociatorBimod.inv]
  simp only [Category.assoc]
  dsimp only [tensorObjπ]
  erw [coequalizer.π_desc_assoc]
  dsimp only [Bimod.AssociatorBimod.invAux]
  simp only [Category.assoc]
  slice_lhs 1 3 => erw [id_tensor_π_preserves_coequalizer_inv_desc]
  dsimp only [bimodTensorRight, Bimod.whiskerRight]
  simp only [Category.assoc]
  erw [ι_colimMap_assoc]
  simp only [parallelPairHom_app_one]
  rw [← comp_whiskerRight_assoc]
  dsimp only [restrictRightUnitIso, Bimod.isoOfIso, Bimod.RightUnitorBimod.hom]
  erw [coequalizer.π_desc]
  dsimp only [restrictedTensorIso]
  erw [coequalizer.π_desc]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma cancellationIso_naturality (M : Mod C R) {N N' : Mod C S} (f : N ⟶ N') :
    (f ▷ (extendScalars φ).obj M).hom ≫ (cancellationIso φ M N').hom =
      (cancellationIso φ M N).hom ≫ ((comap φ).map f ▷ M).hom := by
  apply (cancel_epi (tensorObjπ N ((extendScalars φ).obj M))).1
  apply (cancel_epi (N.X ◁ extendπ φ M)).1
  erw [tensorObjπ_whiskerRight_assoc, whisker_exchange_assoc,
    cancellationIso_π, reassoc_of% cancellationIso_π φ M N,
    tensorObjπ_whiskerRight, associator_inv_naturality_left_assoc]
  have hf : f.hom ▷ S ≫ ((β_ N'.X S).hom ≫ γ[S,N'.X]) =
      ((β_ N.X S).hom ≫ γ[S,N.X]) ≫ f.hom := by
    rw [braiding_naturality_left_assoc, ← act_hom, Category.assoc]
  erw [← comp_whiskerRight_assoc, hf, comp_whiskerRight_assoc]
  rfl

private def cancellationNatIso (M : Mod C R) :
    MonoidalCategory.tensorRight ((extendScalars φ).obj M) ⋙ forget S ≅
      comap φ ⋙ MonoidalCategory.tensorRight M ⋙ forget R :=
  NatIso.ofComponents (cancellationIso φ M) (cancellationIso_naturality φ M)

section Flat

variable [Abelian C]

attribute [local instance] comp_preservesFiniteLimits
  comp_preservesFiniteColimits

/-- Extension of scalars of internal modules preserves flat objects.

Source: Stacks, sites-modules.tex, lemma-flat-change-of-rings; Tag 07A4.
(blueprint: lem-sfb-internal-extension-preserves-flat).

Proof: the bimodule associator and right unitor identify the underlying object of
`N ⊗_S (S ⊗_R M)` with that of `Res N ⊗_R M`, naturally in N. Restriction and the
forgetful functors are exact; forgetful functors reflect limits and colimits. Thus,
if M is flat, tensoring on the right with its extension is exact. Braiding identifies
tensoring on the left with tensoring on the right, proving both flatness conditions.
This also covers the zero algebra and the identity scalar map.
-/
theorem extendScalars_preservesFlat : (extendScalars φ).PreservesFlat where
  flat_obj {M} hM := by
    have := hM.tensorRight.preservesFiniteLimits
    have := hM.tensorRight.preservesFiniteColimits
    have : PreservesFiniteLimits
        (MonoidalCategory.tensorRight ((extendScalars φ).obj M) ⋙ forget S) :=
      preservesFiniteLimits_of_natIso (cancellationNatIso φ M).symm
    have : PreservesFiniteColimits
        (MonoidalCategory.tensorRight ((extendScalars φ).obj M) ⋙ forget S) :=
      preservesFiniteColimits_of_natIso (cancellationNatIso φ M).symm
    have : PreservesFiniteLimits (MonoidalCategory.tensorRight ((extendScalars φ).obj M)) :=
      ⟨fun J _ _ ↦ preservesLimitsOfShape_of_reflects_of_preserves _ (forget S)⟩
    have : PreservesFiniteColimits (MonoidalCategory.tensorRight ((extendScalars φ).obj M)) :=
      ⟨fun J _ _ ↦ preservesColimitsOfShape_of_reflects_of_preserves _ (forget S)⟩
    have : PreservesFiniteLimits (MonoidalCategory.tensorLeft ((extendScalars φ).obj M)) :=
      preservesFiniteLimits_of_natIso
        (BraidedCategory.tensorLeftIsoTensorRight ((extendScalars φ).obj M)).symm
    have : PreservesFiniteColimits (MonoidalCategory.tensorLeft ((extendScalars φ).obj M)) :=
      preservesFiniteColimits_of_natIso
        (BraidedCategory.tensorLeftIsoTensorRight ((extendScalars φ).obj M)).symm
    exact ⟨(exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩,
      (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩⟩

end Flat

end CategoryTheory.Mod
