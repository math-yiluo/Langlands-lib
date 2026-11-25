/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClopenData.ProEtaleClopenTotalTensorKFlatDetectionData
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedDirectImagePairingLax
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal

/-! Ordinary normalized braided tensor restriction along a clopen immersion.

## References

* Tag 0FPQ
* Stacks Project, Modules on Sites, Tags 03EL and 0GMW
-/

@[expose] public noncomputable section
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option Elab.async false
universe t u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures

attribute [local irreducible] SheafOfModules.tensorObjIsoSheafification
  PresheafOfModules.sheafificationAdjunction

attribute [local irreducible] Localization.Monoidal.μ Localization.Monoidal.tensorBifunctor
  Localization.Monoidal.associator Localization.Monoidal.leftUnitor
  Localization.Monoidal.rightUnitor

open CategoryTheory.CochainPullback

section Restriction
universe uC vC uD vD a
variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{a} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{a} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{a} RingCat.{a})]
  [K.HasSheafCompose (forget₂ CommRingCat.{a} RingCat.{a})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{a}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{a}]
  [HasWeakSheafify J AddCommGrpCat.{a}] [HasWeakSheafify K AddCommGrpCat.{a}]
  (v : C ⥤ D) [v.IsContinuous J K] [v.IsCocontinuous J K]
  (R : Sheaf K CommRingCat.{a})

private abbrev restrictionRing := (v.sheafPushforwardContinuous CommRingCat.{a} J K).obj R
private abbrev restriction := SheafOfModules.pushforward.{a} (F := v) (J := J) (K := K)
  (R := (sheafCompose K (forget₂ CommRingCat RingCat)).obj R)
  (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj (restrictionRing (J := J) v R)))

section TensorExtensionality
attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.symmetricCategory

private theorem tensor_ext
    (A : Sheaf J CommRingCat.{a})
    (M N H : SheafOfModules.{a} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
    (f g : M ⊗ N ⟶ H)
    (h : ∀ U x y, f.val.app U (moduleTmul M N U x y) =
      g.val.app U (moduleTmul M N U x y)) : f = g := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).obj)
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification M N).inv).mp
  apply (adj.homEquiv _ H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  ext z
  change f.val.app U ((SheafOfModules.tensorObjIsoSheafification M N).inv.val.app U
      ((adj.unit.app (M.val ⊗ N.val)).app U z)) =
    g.val.app U ((SheafOfModules.tensorObjIsoSheafification M N).inv.val.app U
      ((adj.unit.app (M.val ⊗ N.val)).app U z))
  induction z using TensorProduct.inductionOn with
  | tmul x y => exact h U x y
  | add x y hx hy => simp only [map_add, hx, hy]

end TensorExtensionality

section TensorInvertibility
attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.symmetricCategory

private theorem restriction_tensor_isIso
    (L : (restriction (J := J) v R).LaxMonoidal)
    (hL : SheafOfModules.RingedPushforwardPureTensor v (restrictionRing (J := J) v R) R (𝟙 _) L)
    (M N : SheafOfModules.{a} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)) :
    letI := L
    IsIso (Functor.LaxMonoidal.μ (restriction (J := J) v R) M N) := by
  let := L
  let A := (sheafCompose K (forget₂ CommRingCat RingCat)).obj R
  let B := (sheafCompose J (forget₂ CommRingCat RingCat)).obj (restrictionRing (J := J) v R)
  let Q := restriction (J := J) v R
  let P := PresheafOfModules.pushforward.{a} (F := v) (R := A.obj) (𝟙 B.obj)
  let T := PresheafOfModules.toPresheaf B.obj
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 B.obj)).unit
  let η' := (PresheafOfModules.sheafificationAdjunction (𝟙 A.obj)).unit
  let P₀ := PresheafOfModules.pushforward₀OfCommRingCat v R.obj
  let i (V : PresheafOfModules.{a} A.obj) : P.obj V ≅ P₀.obj V :=
    PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by intros; rfl)
  let e : (Q.obj M).val ⊗ (Q.obj N).val ≅ P.obj (M.val ⊗ N.val) :=
    (i M.val ⊗ᵢ i N.val) ≪≫ Functor.Monoidal.μIso P₀ M.val N.val ≪≫
      (i (M.val ⊗ N.val)).symm
  let a := η.app ((Q.obj M).val ⊗ (Q.obj N).val) ≫
    (SheafOfModules.tensorObjIsoSheafification (Q.obj M) (Q.obj N)).inv.val
  let b := e.hom ≫ P.map (η'.app (M.val ⊗ N.val)) ≫
    P.map (SheafOfModules.tensorObjIsoSheafification M N).inv.val
  let μ := Functor.LaxMonoidal.μ Q M N
  have hab : a ≫ μ.val = b := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    exact hL M N U x y
  have hu : J.W (T.map (P.map (η'.app (M.val ⊗ N.val)))) := by
    change J.W (Functor.whiskerLeft v.op
      ((PresheafOfModules.toPresheaf A.obj).map (η'.app (M.val ⊗ N.val))))
    dsimp only [η']
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    have : Presheaf.IsLocallyInjective J
        (Functor.whiskerLeft v.op (toSheafify K (M.val ⊗ N.val).presheaf)) :=
      Presheaf.isLocallyInjective_whisker J K v _
    have : Presheaf.IsLocallySurjective J
        (Functor.whiskerLeft v.op (toSheafify K (M.val ⊗ N.val).presheaf)) :=
      Presheaf.isLocallySurjective_whisker J K v _
    exact J.W_of_isLocallyBijective _
  have : IsIso (SheafOfModules.tensorObjIsoSheafification M N).inv.val := by
    change IsIso ((SheafOfModules.forget A).map
      (SheafOfModules.tensorObjIsoSheafification M N).inv)
    infer_instance
  have : IsIso
      (SheafOfModules.tensorObjIsoSheafification (Q.obj M) (Q.obj N)).inv.val := by
    change IsIso ((SheafOfModules.forget B).map
      (SheafOfModules.tensorObjIsoSheafification (Q.obj M) (Q.obj N)).inv)
    infer_instance
  have hb : J.W (T.map b) := by
    dsimp only [b]
    rw [T.map_comp, T.map_comp]
    exact J.W.comp_mem _ _ (J.W.of_isIso _) (J.W.comp_mem _ _ hu (J.W.of_isIso _))
  have ha : J.W (T.map a) := by
    dsimp only [a]
    rw [T.map_comp]
    apply J.W.comp_mem _ _ _ (J.W.of_isIso _)
    dsimp only [T, η]
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact J.W_toSheafify _
  have hm : J.W (T.map μ.val) := by
    apply J.W.of_precomp (W' := J.W) (T.map a) (T.map μ.val) ha
    rw [← T.map_comp, hab]
    exact hb
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf B)]
  exact (J.W_sheafToPresheaf_map_iff_isIso _).mp hm

end TensorInvertibility
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

omit [J.WEqualsLocallyBijective AddCommGrpCat.{a}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{a}]
  [HasWeakSheafify J AddCommGrpCat.{a}] [HasWeakSheafify K AddCommGrpCat.{a}]
  [v.IsCocontinuous J K] in
private theorem restriction_unit_isIso
    (L : (restriction (J := J) v R).LaxMonoidal)
    (hε : ∀ (U : Cᵒᵖ) (r : (restrictionRing (J := J) v R).obj.obj U),
      (@Functor.LaxMonoidal.ε _ _ _ _ _ _ (restriction (J := J) v R) L).val.app U r = r) :
    letI := L
    IsIso (Functor.LaxMonoidal.ε (restriction (J := J) v R)) := by
  let := L
  let B := (sheafCompose J (forget₂ CommRingCat RingCat)).obj
    (restrictionRing (J := J) v R)
  let Q := restriction (J := J) v R
  let e : (𝟙_ (SheafOfModules.{a} B)) ≅ Q.obj (𝟙_ _) :=
    (SheafOfModules.fullyFaithfulForget B).preimageIso
      (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by intros; rfl))
  have he : Functor.LaxMonoidal.ε Q = e.hom := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    exact hε U r
  rw [he]
  infer_instance

omit [K.WEqualsLocallyBijective AddCommGrpCat.{a}]
  [HasWeakSheafify K AddCommGrpCat.{a}] [v.IsCocontinuous J K] in
private theorem restriction_braided
    (L : (restriction (J := J) v R).LaxMonoidal)
    (hL : SheafOfModules.RingedPushforwardPureTensor v
      (restrictionRing (J := J) v R) R (𝟙 _) L) :
    letI := L
    ∀ M N, Functor.LaxMonoidal.μ (restriction (J := J) v R) M N ≫
      (restriction (J := J) v R).map (β_ M N).hom =
        (β_ ((restriction (J := J) v R).obj M)
          ((restriction (J := J) v R).obj N)).hom ≫
            Functor.LaxMonoidal.μ (restriction (J := J) v R) N M := by
  let := L
  intro M N
  apply tensor_ext (restrictionRing (J := J) v R) _ _ _
  intro U x y
  change (β_ M N).hom.val.app (v.op.obj U)
      ((Functor.LaxMonoidal.μ (restriction (J := J) v R) M N).val.app U
        (moduleTmul _ _ U x y)) =
    (Functor.LaxMonoidal.μ (restriction (J := J) v R) N M).val.app U
      ((β_ ((restriction (J := J) v R).obj M)
        ((restriction (J := J) v R).obj N)).hom.val.app U (moduleTmul _ _ U x y))
  rw [hL M N U x y, moduleTmul_braiding, moduleTmul_braiding, hL N M U y x]

end Restriction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Scheme.ProEt

attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.symmetricCategory

/-- Ordinary restriction admits its canonical normalized braided structure. -/
theorem clopen_ordinary_tensor_normalization
    {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j] [IsClosedImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    ∃ h : (ClopenData.clopenTensorRestriction.{t, u} j R).Braided,
      ∀ (F H : ClopenData.clopenTensorModules.{t, u} R) (U : Y.ProEt)
        (x : F.val.obj (op ((MorphismProperty.Over.map ⊤
          (inferInstance : WeaklyEtale j)).obj U)))
        (y : H.val.obj (op ((MorphismProperty.Over.map ⊤
          (inferInstance : WeaklyEtale j)).obj U))),
        (ClopenData.clopenTensorComparison.{t, u} j R h F H).hom.val.app (op U)
          (ClopenData.clopenTensorPure.{t, u} R F H _ x y) =
        ClopenData.clopenTensorPure.{t, u} ((ClopenData.clopenTensorRings.{t, u} j).obj R)
          ((ClopenData.clopenTensorRestriction.{t, u} j R).obj F)
          ((ClopenData.clopenTensorRestriction.{t, u} j R).obj H) (op U) x y := by
  classical
  let v : Y.ProEt ⥤ X.ProEt :=
    MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)
  let : v.IsContinuous (topology Y) (topology X) :=
    isContinuous_overMap (inferInstance : WeaklyEtale j)
  let : v.IsCocontinuous (topology Y) (topology X) :=
    isCocontinuous_overMap (inferInstance : WeaklyEtale j)
  let R' := ClopenData.clopenTensorRings.{t, u} j |>.obj R
  obtain ⟨L, hL, hε, _⟩ :=
    SheafOfModules.exists_unique_ringedPushforward_laxMonoidal v R' R (𝟙 _)
  let Q := ClopenData.clopenTensorRestriction.{t, u} j R
  let : Q.LaxMonoidal := L
  have : IsIso (Functor.LaxMonoidal.ε Q) := restriction_unit_isIso v R L hε
  have : ∀ M N, IsIso (Functor.LaxMonoidal.μ Q M N) :=
    fun M N ↦ restriction_tensor_isIso v R L hL M N
  let : Q.Monoidal := Functor.Monoidal.ofLaxMonoidal Q
  let h : Q.Braided :=
    { toMonoidal := inferInstance
      braided := restriction_braided v R L hL }
  refine ⟨h, ?_⟩
  intro M N U x y
  let := h
  have hp := hL M N (op U) x y
  have hi := congrArg
    (fun f ↦ f.val.app (op U) (ClopenData.clopenTensorPure.{t, u} R'
      (Q.obj M) (Q.obj N) (op U) x y))
    (Functor.Monoidal.μIso Q M N).hom_inv_id
  exact (congrArg
    ((ClopenData.clopenTensorComparison.{t, u} j R h M N).hom.val.app (op U)) hp).symm.trans hi

end AlgebraicGeometry.Scheme.ProEt
