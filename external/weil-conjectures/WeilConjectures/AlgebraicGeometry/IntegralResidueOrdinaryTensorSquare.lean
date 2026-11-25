/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralReductionTensor
public import WeilConjectures.AlgebraicGeometry.IntegralResidueOrdinaryMonoidal
import all WeilConjectures.AlgebraicGeometry.IntegralResiduePullOrdinaryUnit

/-! # The ordinary balanced scalar tensor square

Source: Bhatt--Scholze, Remark 6.8.15 and Lemma 6.5.9(5), p. 51.
(auxiliary; not a blueprint node)
-/

@[expose] public section
set_option autoImplicit false
universe v u u'
open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor
attribute [local irreducible] Mod.extendScalarsIsoComapInv
private theorem action_pull
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [HasCoequalizers C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    {D : Type u'} [Category.{v} D] [MonoidalCategory D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    [BraidedCategory D] [MonoidalClosed D] [HasEqualizers D]
    (U : C ⥤ D) [U.Braided] {R : C} [MonObj R] [IsCommMonObj R]
    {S : D} [MonObj S] [IsCommMonObj S] (a : U.obj R ⟶ S) [IsMonHom a] [IsIso a]
    (N : Mod C R) :
    let z := (Mod.extendScalarsIsoComapInv a).inv.app ((U.mapMod R).obj N)
    U.map γ[R,N.X] ≫ z.hom =
      Functor.OplaxMonoidal.δ U R N.X ≫ a ▷ U.obj N.X ≫
        S ◁ z.hom ≫ γ[S,((Mod.extendScalars a).obj ((U.mapMod R).obj N)).X] := by
  dsimp only
  rw [← Mod.act_hom]
  change _ = Functor.OplaxMonoidal.δ U R N.X ≫ a ▷ U.obj N.X ≫
    (inv a ▷ U.obj N.X ≫ Functor.LaxMonoidal.μ U R N.X ≫ U.map γ[R,N.X]) ≫ _
  simp only [Category.assoc]
  rw [← comp_whiskerRight_assoc, IsIso.hom_inv_id, id_whiskerRight,
    Category.id_comp, Functor.Monoidal.δ_μ_assoc]

private theorem extension_projection
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [HasCoequalizers C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    {D : Type u'} [Category.{v} D] [MonoidalCategory D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    [BraidedCategory D] [MonoidalClosed D] [HasEqualizers D]
    (U : C ⥤ D) [U.Braided] {R S : C} [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    {R' S' : D} [MonObj R'] [IsCommMonObj R'] [MonObj S'] [IsCommMonObj S']
    (φ : R ⟶ S) [IsMonHom φ] (ψ : R' ⟶ S') [IsMonHom ψ]
    (a : U.obj S ⟶ S') [IsMonHom a] [IsIso a]
    (M : Mod C R) (M' : Mod D R')
    (p : (Mod.extendScalars a).obj ((U.mapMod S).obj ((Mod.extendScalars φ).obj M)) ⟶
      (Mod.extendScalars ψ).obj M') (u : U.obj M.X ⟶ M'.X)
    (h : U.map (Mod.extendUnitHom φ M) ≫
        ((Mod.extendScalarsIsoComapInv a).inv.app
          ((U.mapMod S).obj ((Mod.extendScalars φ).obj M))).hom ≫ p.hom =
      u ≫ Mod.extendUnitHom ψ M') :
    U.map (Mod.extendπ φ M) ≫
        ((Mod.extendScalarsIsoComapInv a).inv.app
          ((U.mapMod S).obj ((Mod.extendScalars φ).obj M))).hom ≫ p.hom =
      Functor.OplaxMonoidal.δ U S M.X ≫ (a ⊗ₘ u) ≫ Mod.extendπ ψ M' := by
  have ha := action_pull U a ((Mod.extendScalars φ).obj M)
  dsimp only at ha
  rw [← Mod.whiskerLeft_extendUnitHom_smul', Functor.map_comp]
  erw [Category.assoc, reassoc_of% ha]
  erw [← Functor.OplaxMonoidal.δ_natural_right_assoc, whisker_exchange_assoc, Mod.act_hom]
  simp only [← whiskerLeft_comp_assoc]
  rw [h, whiskerLeft_comp_assoc, Mod.whiskerLeft_extendUnitHom_smul']
  rw [MonoidalCategory.tensorHom_def, Category.assoc]

local instance instEssentiallySmallProfinite_integralResidueOrdinaryTensorSquare
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local irreducible] upperStarLowerStarAdjunction comapUpperStarIso
  comapLowerStarIso profinitePointModuleForgetPullbackIso
-- Coefficient pullback compares several explicitly constructed module actions.
private theorem scalar_unit_inv
    (Λ A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] [MonObj A] [IsCommMonObj A]
    (φ : Λ ⟶ A) [IsMonHom φ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    let TY := Mod.extendScalars (coefficientMap φ Y)
    let U := ProEtale.upperStar Ab.{u + 1} f
    U.map (Mod.extendUnitHom (coefficientMap φ Y) M) ≫
      (profinitePointModuleForgetPullbackIso A f).inv.app (TY.obj M) ≫
      ((pullIso φ f).inv.app M).hom =
    (profinitePointModuleForgetPullbackIso Λ f).inv.app M ≫
      Mod.extendUnitHom (coefficientMap φ X) ((f)^*⟦Λ⟧.obj M) := by
  dsimp only
  have h := ordinaryScalarUnit φ f M
  have h' := congrArg (fun k ↦ k ≫
    (Mod.comap (coefficientMap φ X)).map ((pullIso φ f).inv.app M)) h
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app] at h'
  have hh := congrArg (fun k ↦ k.hom) h'
  simp only [Mod.comp_hom', Mod.comap_map_hom] at hh
  erw [Mod.id_hom', Category.comp_id] at hh
  have hn := (profinitePointModuleForgetPullbackIso Λ f).hom.naturality
    ((Mod.extendRestrictAdjunction (coefficientMap φ Y)).unit.app M)
  dsimp only [Functor.comp_map, Mod.forget] at hn
  have hq := comapUpperStar_inv_forget φ f
    ((Mod.extendScalars (coefficientMap φ Y)).obj M)
  have hq' : ((comapUpperStarIso φ f).inv.app
      ((Mod.extendScalars (coefficientMap φ Y)).obj M)).hom =
    (profinitePointModuleForgetPullbackIso Λ f).hom.app
      ((Mod.comap (coefficientMap φ Y)).obj
        ((Mod.extendScalars (coefficientMap φ Y)).obj M)) ≫
      (profinitePointModuleForgetPullbackIso A f).inv.app
        ((Mod.extendScalars (coefficientMap φ Y)).obj M) := by
    erw [← hq, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  erw [hq'] at hh
  simp only [← Category.assoc] at hh
  erw [hn] at hh
  have hhh := congrArg (fun k ↦
    (profinitePointModuleForgetPullbackIso Λ f).inv.app M ≫ k) hh
  simp only [Category.assoc] at hhh
  erw [Iso.inv_hom_id_app_assoc] at hhh
  exact hhh
end AlgebraicGeometry.ProEtale.CondensedRing
namespace AlgebraicGeometry.ProEtale.CondensedRing
-- Coefficient pullback compares several explicitly constructed module actions.
private theorem pull_tensor_π
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    let U := ProEtale.upperStar Ab.{u + 1} f
    let F := (f)^*⟦Λ⟧
    let e := profinitePointModuleForgetPullbackIso Λ f
    letI := residueOrdinaryUpperStarMonoidal Λ f
    U.map (Mod.tensorObjπ M N) ≫ e.inv.app (M ⊗ N) ≫
        (Functor.OplaxMonoidal.δ F M N).hom =
      Functor.OplaxMonoidal.δ U M.X N.X ≫
        (e.inv.app M ⊗ₘ e.inv.app N) ≫ Mod.tensorObjπ (F.obj M) (F.obj N) := by
  dsimp only
  let U := ProEtale.upperStar Ab.{u + 1} f
  let : U.Braided :=
    { toMonoidal := inferInstance
      braided X Y := Functor.LaxBraided.braided (F := U) X Y }
  let ρ := (asIso (condensedPullbackHom Λ f)).inv
  let := Mod.ResidueOrdinary.mapModComapMonoidal ρ
  let i := Functor.isoWhiskerLeft (U.mapMod (condensedRingObj Λ Y))
    (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f))
  have hd := Functor.Monoidal.transport_δ i.symm M N
  have hdh := congrArg (fun k ↦ k.hom) hd
  dsimp only [Iso.symm_inv, Iso.symm_hom, Mod.comp_hom'] at hdh
  erw [hdh]
  erw [Iso.inv_hom_id_app_assoc]
  have ht := Mod.ResidueOrdinary.tensorComparison_π ρ M N
  erw [reassoc_of% ht]
  erw [Mod.tensorObjπ_whiskerRight_assoc, Mod.tensorObjπ_whiskerLeft]
  rw [Functor.Monoidal.inv_μ]
  dsimp only [MonoidalCategory.tensorHom_def, profinitePointModuleForgetPullbackIso,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app]
  rfl
end AlgebraicGeometry.ProEtale.CondensedRing
namespace AlgebraicGeometry.ProEtale.CondensedRing
-- Coefficient pullback compares several explicitly constructed module actions.
private theorem pull_extend_π
    (Λ A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] [MonObj A] [IsCommMonObj A]
    (φ : Λ ⟶ A) [IsMonHom φ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    let TY := Mod.extendScalars (coefficientMap φ Y)
    let U := ProEtale.upperStar Ab.{u + 1} f
    U.map (Mod.extendπ (coefficientMap φ Y) M) ≫
      (profinitePointModuleForgetPullbackIso A f).inv.app (TY.obj M) ≫
      ((pullIso φ f).inv.app M).hom =
    Functor.OplaxMonoidal.δ U (condensedRingObj A Y) M.X ≫
      (condensedPullbackHom A f ⊗ₘ
        (profinitePointModuleForgetPullbackIso Λ f).inv.app M) ≫
      Mod.extendπ (coefficientMap φ X) ((f)^*⟦Λ⟧.obj M) := by
  dsimp only
  let U := ProEtale.upperStar Ab.{u + 1} f
  let : U.Braided :=
    { toMonoidal := inferInstance
      braided X Y := Functor.LaxBraided.braided (F := U) X Y }
  exact extension_projection U (coefficientMap φ Y) (coefficientMap φ X)
    (condensedPullbackHom A f) M ((f)^*⟦Λ⟧.obj M) ((pullIso φ f).inv.app M)
    ((profinitePointModuleForgetPullbackIso Λ f).inv.app M) (scalar_unit_inv Λ A φ f M)

end AlgebraicGeometry.ProEtale.CondensedRing
namespace AlgebraicGeometry.ProEtale.CondensedRing
-- Coefficient pullback compares several explicitly constructed module actions.
private theorem pull_regular_η
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    letI := residueOrdinaryUpperStarMonoidal A f
    (profinitePointModuleForgetPullbackIso A f).inv.app
        (Mod.regular (condensedRingObj A Y)) ≫
      (Functor.OplaxMonoidal.η (f)^*⟦A⟧).hom = condensedPullbackHom A f := by
  let U := ProEtale.upperStar Ab.{u + 1} f
  let : U.Braided :=
    { toMonoidal := inferInstance
      braided X Y := Functor.LaxBraided.braided (F := U) X Y }
  let ρ := (asIso (condensedPullbackHom A f)).inv
  let := Mod.ResidueOrdinary.mapModComapMonoidal ρ
  let i := Functor.isoWhiskerLeft (U.mapMod (condensedRingObj A Y))
    (Mod.extendScalarsIsoComapInv (condensedPullbackHom A f))
  have hd := Functor.Monoidal.transport_η i.symm
  have hdh := congrArg (fun k ↦ k.hom) hd
  dsimp only [Iso.symm_inv, Mod.comp_hom'] at hdh
  erw [hdh]
  erw [Iso.inv_hom_id_app_assoc]
  change inv ρ = condensedPullbackHom A f
  simp only [ρ, asIso_inv, IsIso.inv_inv]

/-- Ordinary pullback of a restricted regular module, using the restriction square
and the inverse monoidal unit of residue pullback. Naming this construction before
specializing the coefficients avoids expanding the concrete integral ring instances.

Source: Bhatt--Scholze, Remark 6.8.15; the fixed coefficient identification in the
proof of Lemma 6.5.9(5). (auxiliary; not a blueprint node) -/
@[irreducible] noncomputable def residueOrdinaryRestrictedRegularPullIso
    (Λ A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] [MonObj A] [IsCommMonObj A]
    (φ : Λ ⟶ A) [IsMonHom φ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (f)^*⟦Λ⟧.obj
        ((Mod.comap (coefficientMap φ Y)).obj (Mod.regular (condensedRingObj A Y))) ≅
      (Mod.comap (coefficientMap φ X)).obj (Mod.regular (condensedRingObj A X)) := by
  let SX := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap φ X)
  letI := residueOrdinaryUpperStarMonoidal A f
  exact (comapUpperStarIso φ f).symm.app (Mod.regular (condensedRingObj A Y)) ≪≫
    SX.mapIso (Functor.Monoidal.εIso (f)^*⟦A⟧).symm

-- Coefficient pullback compares several explicitly constructed module actions.
private theorem coefficient_pull_hom
    (Λ A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] [MonObj A] [IsCommMonObj A]
    (φ : Λ ⟶ A) [IsMonHom φ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (profinitePointModuleForgetPullbackIso Λ f).inv.app
        ((Mod.comap (coefficientMap φ Y)).obj (Mod.regular (condensedRingObj A Y))) ≫
      (residueOrdinaryRestrictedRegularPullIso Λ A φ f).hom.hom = condensedPullbackHom A f := by
  unfold residueOrdinaryRestrictedRegularPullIso
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom,
    Mod.comp_hom', Mod.comap_map_hom]
  let N := Mod.regular (condensedRingObj A Y)
  have hq := comapUpperStar_inv_forget φ f N
  have hq' : ((comapUpperStarIso φ f).inv.app N).hom =
    (profinitePointModuleForgetPullbackIso Λ f).hom.app
      ((Mod.comap (coefficientMap φ Y)).obj N) ≫
      (profinitePointModuleForgetPullbackIso A f).inv.app N := by
    erw [← hq, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  erw [hq', Category.assoc, Iso.inv_hom_id_app_assoc]
  exact pull_regular_η A f

attribute [local irreducible] Mod.monoidalCategoryStruct
  Mod.tensorObjπ Mod.extendπ residueOrdinaryUpperStarMonoidal

-- Compare the constructed module maps on their explicit coequalizer presentations.
/-- The ordinary scalar pull square is the balanced tensor comparison.
Source: Bhatt--Scholze, Remark 6.8.15 and the ordinary tensor-pullback identity
in the proof of Lemma 6.5.9(5), p. 51; explicit comparison of the canonical maps.
(auxiliary; not a blueprint node)

Proof. Write TX, TY for extension, SX, SY for restriction, F for integral
pullback and G for pullback after the coefficient change. The inverse scalar
comparison p is determined by the ordinary extension unit identity
F(etaY) q = etaX SX(p), with q the inverse restriction/pullback comparison.
Forget module actions and precompose the asserted equality with F applied to
the coequalizer projection defining TY(M). Under extendComapTensorIso this
projection is the balanced tensor projection. The defining equation of the
strong monoidal pullback tensorator identifies its composite with the ambient
inverse-image tensorator followed by the balanced tensor projection on X.
Use the extension unit identity to replace p inverse on the unit, then use
linearity over the residue ring to replace it on the whole coequalizer
projection: S tensor eta followed by the S-action is precisely that projection.
The inverse restriction comparison has identity underlying sheaf map after
the coefficient pullback identifications. The coefficient isomorphism e has
the same property followed by the inverse monoidal unit on the regular module.
Its unit cancels the pulled-back regular-module coefficient in the tensorator.
Consequently both composites on the free tensor presentation are the ambient
pullback tensorator, the pulled-back coefficient identification, and the same
balanced projection on X. Equality follows by the epimorphism of that
projection and faithfulness of forgetting module actions. No flatness or
nonempty-site hypothesis is used. -/
theorem residueOrdinaryTensorPull_module
    (Λ A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] [MonObj A] [IsCommMonObj A]
    (φ : Λ ⟶ A) [IsMonHom φ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    let F := (f)^*⟦Λ⟧
    let TY := Mod.extendScalars (coefficientMap φ Y)
    let SX := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (coefficientMap φ X)
    let SY := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (coefficientMap φ Y)
    let B := SY.obj (Mod.regular (condensedRingObj A Y))
    let e := residueOrdinaryRestrictedRegularPullIso Λ A φ f
    letI := residueOrdinaryUpperStarMonoidal Λ f
    (comapUpperStarIso φ f).inv.app (TY.obj M) ≫
      SX.map ((pullIso φ f).inv.app M) ≫
      (Mod.extendComapTensorIso (coefficientMap φ X)).hom.app (F.obj M) =
    F.map ((Mod.extendComapTensorIso (coefficientMap φ Y)).hom.app M) ≫
      Functor.OplaxMonoidal.δ F B M ≫ e.hom ▷ F.obj M := by
  dsimp only
  let U := ProEtale.upperStar Ab.{u + 1} f
  let F := (f)^*⟦Λ⟧
  let TY := Mod.extendScalars (coefficientMap φ Y)
  let SY := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (coefficientMap φ Y)
  let B := SY.obj (Mod.regular (condensedRingObj A Y))
  let _ := residueOrdinaryUpperStarMonoidal Λ f
  let e := profinitePointModuleForgetPullbackIso Λ f
  let v := U.map (Mod.extendπ (coefficientMap φ Y) M) ≫ e.inv.app (SY.obj (TY.obj M))
  have : Epi v := by dsimp only [v]; infer_instance
  apply Mod.hom_ext
  apply (cancel_epi v).1
  dsimp only [v]
  simp only [Mod.comp_hom', Mod.comap_map_hom, Category.assoc]
  have hq := comapUpperStar_inv_forget φ f (TY.obj M)
  have hq' : e.inv.app (SY.obj (TY.obj M)) ≫
      ((comapUpperStarIso φ f).inv.app (TY.obj M)).hom =
    (profinitePointModuleForgetPullbackIso A f).inv.app (TY.obj M) := by
    apply (cancel_mono ((profinitePointModuleForgetPullbackIso A f).hom.app (TY.obj M))).1
    erw [Category.assoc, hq, Iso.inv_hom_id_app, Iso.inv_hom_id_app]
    rfl
  slice_lhs 2 3 => exact hq'
  have hn := e.inv.naturality ((Mod.extendComapTensorIso (coefficientMap φ Y)).hom.app M)
  dsimp only [Functor.comp_map, Mod.forget] at hn
  slice_rhs 2 3 => exact hn.symm
  slice_rhs 1 2 => exact (U.map_comp _ _).symm
  have htπ : Mod.extendπ (coefficientMap φ Y) M ≫
      ((Mod.extendComapTensorIso (coefficientMap φ Y)).hom.app M).hom =
    Mod.tensorObjπ B M := by
    exact Mod.extendπ_extendDescHom _ _ _
  slice_rhs 1 1 => exact congrArg U.map htπ
  slice_rhs 1 3 => exact pull_tensor_π Λ f B M
  slice_lhs 1 3 => exact pull_extend_π Λ A φ f M
  have hxπ : Mod.extendπ (coefficientMap φ X) (F.obj M) ≫
      ((Mod.extendComapTensorIso (coefficientMap φ X)).hom.app (F.obj M)).hom =
    Mod.tensorObjπ ((Mod.comap (coefficientMap φ X)).obj
      (Mod.regular (condensedRingObj A X))) (F.obj M) := by
    exact Mod.extendπ_extendDescHom _ _ _
  slice_lhs 3 4 => exact hxπ
  slice_rhs 3 4 => exact Mod.tensorObjπ_whiskerRight _
  simp only [MonoidalCategory.tensorHom_def, Category.assoc]
  erw [whisker_exchange_assoc]
  erw [← comp_whiskerRight_assoc, coefficient_pull_hom Λ A φ f]
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
