/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import WeilConjectures.Topology.InverseImageOperationExt
import WeilConjectures.AlgebraicGeometry.SheafTensorPushoutCancellation
/-! # Affine module tensor BaseChange

Source: Stacks Project, Morphisms, Lemma 01SB.
(blueprint: lem-weil-pbc-affine-module-tensor-base-change).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {U X : Scheme.{u}} (f : U ⟶ X)

set_option hygiene false in
local notation "𝓙" T => Opens.grothendieckTopology T
set_option hygiene false in
local notation "𝓡" S => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj S
set_option hygiene false in
local notation "𝓻" a => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map a
set_option hygiene false in
local notation "A" => (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj U.sheaf
set_option hygiene false in
local notation "ρ" => (show X.sheaf ⟶ A from ⟨f.c⟩)
set_option hygiene false in
local notation "R" => SheafOfModules.pushforward.{u} (F := Opens.map f.base)
  (S := 𝓡 A) (R := U.ringCatSheaf) (𝟙 (𝓡 A))
set_option hygiene false in
local notation "S" => SheafOfModules.restrictScalars.{u} (𝓻 ρ)
set_option hygiene false in
local notation "I" => TopCat.Sheaf.inverseImageModule f.base A
set_option hygiene false in
local notation "IA" => TopCat.Sheaf.inverseImageRing f.base A
set_option hygiene false in
local notation "r₀" => tensorPullbackRingMap f
set_option hygiene false in
local notation "t₀" => (TopCat.Sheaf.inverseImageConstruction f.base CommRingCat.{u}).map ρ
set_option hygiene false in
local notation "e₀" =>
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f.base) CommRingCat.{u} (𝓙 X) (𝓙 U)).homEquiv A U.sheaf).symm (𝟙 A)
set_option hygiene false in
local notation "adj₀" => Classical.choose (exists_tensorPullbackAdjunction f)

private def extensionFunctor {T : TopCat.{u}} {C D : T.Sheaf CommRingCat.{u}}
    (α : C ⟶ D) : SheafOfModules.{u}
      ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj C) ⥤
      SheafOfModules.{u} ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj D) where
  obj M := SheafOfModules.changeOfRings.{u, u, u} α M
  map a := SheafOfModules.changeOfRingsHom.{u, u, u} α _ a
  map_id M := by
    unfold SheafOfModules.changeOfRingsHom
    have hp : (show SheafOfModules.changeOfRingsPresheaf.{u, u, u} α M ⟶
        SheafOfModules.changeOfRingsPresheaf.{u, u, u} α M from
      { app := fun W ↦ (ModuleCat.extendScalars (α.hom.app W).hom).map
          ((show M ⟶ M from 𝟙 M).val.app W)
        naturality := SheafOfModules.changeOfRingsHom_naturality α M (𝟙 M) }) = 𝟙 _ := by
      apply PresheafOfModules.hom_ext
      intro W
      exact (ModuleCat.extendScalars (α.hom.app W).hom).map_id _
    exact (congrArg
      (fun q ↦ (PresheafOfModules.sheafification
        (𝟙 ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj D).obj)).map q)
      hp).trans (CategoryTheory.Functor.map_id _ _)
  map_comp a c := by
    unfold SheafOfModules.changeOfRingsHom
    rw [← CategoryTheory.Functor.map_comp]
    congr 1
    apply PresheafOfModules.hom_ext
    intro W
    exact (ModuleCat.extendScalars (α.hom.app W).hom).map_comp _ _

private def inverseFunctor {T T' : TopCat.{u}} (g : T ⟶ T')
    (C : T'.Sheaf CommRingCat.{u}) : SheafOfModules.{u}
      ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj C) ⥤
      SheafOfModules.{u} ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (TopCat.Sheaf.inverseImageRing g C)) where
  obj M := TopCat.Sheaf.inverseImageModule g C M
  map a := TopCat.Sheaf.inverseImageModuleMap g C _ a
  map_id M := by
    ext W m
    simp [TopCat.Sheaf.inverseImageModuleMap, PresheafOfModules.homMk]
    rfl
  map_comp a c := by
    ext W m
    simp [TopCat.Sheaf.inverseImageModuleMap, PresheafOfModules.homMk]
    rfl

private theorem inverseRestrict_smul (G : SheafOfModules.{u} (𝓡 A))
    (W : (Opens U)ᵒᵖ) (r : (TopCat.Sheaf.inverseImageRing f.base X.sheaf).obj.obj W)
    (m : (I G).val.obj W) :
    @SMul.smul _ _ (TopCat.Sheaf.inverseImageModuleInstances f.base X.sheaf
      ((S).obj G) W).toSMul r m =
    @SMul.smul _ _ (TopCat.Sheaf.inverseImageModuleInstances f.base A G W).toSMul
      ((t₀).hom.app W r) m := by
  let M := (S).obj G
  let hM := Classical.choose_spec (TopCat.Sheaf.exists_inverseImageModuleInstances
    f.base X.sheaf M)
  let hG := Classical.choose_spec (TopCat.Sheaf.exists_inverseImageModuleInstances
    f.base A G)
  apply TopCat.Sheaf.inverseImageOperation_ext f.base X.sheaf
    ((SheafOfModules.toSheaf _).obj M) (TopCat.Sheaf.inverseImageAb f.base A G)
    (fun W r m ↦ @SMul.smul _ _
      (TopCat.Sheaf.inverseImageModuleInstances f.base X.sheaf M W).toSMul r m)
    (fun W r m ↦ @SMul.smul _ _
      (TopCat.Sheaf.inverseImageModuleInstances f.base A G W).toSMul ((t₀).hom.app W r) m)
    (by
      intro V W i r m
      exact hM.1 i r m)
    (by
      intro V W i r m
      erw [hG.1]
      congr 1
      exact ConcreteCategory.congr_hom ((t₀).hom.naturality i).symm r)
    (by
      intro V r m
      let adjR := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (Opens.map f.base) CommRingCat.{u} (𝓙 X) (𝓙 U)
      have hn : (t₀).hom.app ((Opens.map f.base).op.obj V)
          ((adjR.unit.app X.sheaf).hom.app V r) =
          (adjR.unit.app A).hom.app V ((ρ).hom.app V r) :=
        congrArg (fun a ↦ a.hom.app V r) (adjR.unit_naturality ρ)
      erw [hn]
      exact (hM.2 V r m).symm.trans (hG.2 V ((ρ).hom.app V r) m)
      )
    W r m

private def inverseRestrictIso (G : SheafOfModules.{u} (𝓡 A)) :
    (SheafOfModules.restrictScalars (𝓻 t₀)).obj (I G) ≅
      TopCat.Sheaf.inverseImageModule f.base X.sheaf ((S).obj G) where
  hom := ⟨PresheafOfModules.homMk (𝟙 _) (fun W r m ↦ by
    exact (inverseRestrict_smul f G W r m).symm)⟩
  inv := ⟨PresheafOfModules.homMk (𝟙 _) (fun W r m ↦ by
    exact inverseRestrict_smul f G W r m)⟩
  hom_inv_id := by ext W m; rfl
  inv_hom_id := by ext W m; rfl

private theorem extensionFunctor_unit {T : TopCat.{u}} {C D : T.Sheaf CommRingCat.{u}}
    (α : C ⟶ D) {M N : SheafOfModules.{u}
      ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj C)}
    (a : M ⟶ N) (W : (TopologicalSpace.Opens T)ᵒᵖ)
    (x : (SheafOfModules.changeOfRingsPresheaf.{u, u, u} α M).obj W) :
    ((extensionFunctor α).map a).val.app W
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj D).obj)).unit.app
          (SheafOfModules.changeOfRingsPresheaf.{u, u, u} α M)).app W x) =
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj D).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf.{u, u, u} α N)).app W
          ((ModuleCat.extendScalars (α.hom.app W).hom).map (a.val.app W) x) := by
  let p : SheafOfModules.changeOfRingsPresheaf.{u, u, u} α M ⟶
      SheafOfModules.changeOfRingsPresheaf.{u, u, u} α N :=
    { app := fun V ↦ (ModuleCat.extendScalars (α.hom.app V).hom).map (a.val.app V)
      naturality := SheafOfModules.changeOfRingsHom_naturality α M a }
  exact congrArg (fun q ↦ q.app W x)
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj D).obj)).unit_naturality p)

-- The unit calculation unfolds two scalar restrictions and the chosen adjunction.
/-- Base change across the ring-sheaf pushout identifies extension of the inverse-image
algebra module with tensor pullback after scalar restriction.
Source: Stacks Project, Morphisms, Lemma 01SB, construction of h and elucidation.
Proof: Form the inverse-image module functor and extend along t, with the sheafified
sectionwise map id tensor inverse-image(a). These maps preserve identity and composition.
On stalks the pushout identifies B with O_U tensor over inverse-image O_X with
inverse-image A. The balanced tensor universal property gives inverse maps between
B tensor over inverse-image A with inverse-image G and O_U tensor over inverse-image O_X
with inverse-image G, sending (b tensor a) tensor g to b tensor ag and b tensor g to
(b tensor 1) tensor g. They commute with restriction and sheafification and hence give
the natural isomorphism κ. The canonical unit formula for the chosen pullback adjunction
then gives κ inverse applied to the unit as the sheafification of 1 tensor η(g).
This argument includes the zero ring and zero module: both inverse maps are still given
by the balanced universal property.
(blueprint: lem-weil-pbc-affine-module-tensor-base-change). -/
theorem affine_module_tensor_baseChange
    (B : U.toTopCat.Sheaf CommRingCat.{u}) (b : U.sheaf ⟶ B) (t : IA ⟶ B)
    (hpush : IsPushout r₀ t₀ b t) :
      ∃ (P : SheafOfModules.{u} (𝓡 A) ⥤ SheafOfModules.{u} (𝓡 B))
        (pobj : ∀ G, P.obj G = SheafOfModules.changeOfRings.{u, u, u} t (I G))
        (κ : P ⋙ SheafOfModules.restrictScalars (𝓻 b) ≅ S ⋙ tensorPullback f),
        (∀ (G G' : SheafOfModules.{u} (𝓡 A)) (a : G ⟶ G'),
          P.map a = eqToHom (pobj G) ≫
            SheafOfModules.changeOfRingsHom.{u, u, u} t (I G)
              (TopCat.Sheaf.inverseImageModuleMap f.base A G a) ≫
            eqToHom (pobj G').symm) ∧
        (∀ (G : SheafOfModules.{u} (𝓡 A)) (V : (Opens X)ᵒᵖ) (g : G.val.obj V),
          ((eqToHom (pobj G)).val.app ((Opens.map f.base).op.obj V))
            ((κ.inv.app G).val.app ((Opens.map f.base).op.obj V)
              (((adj₀).unit.app ((S).obj G)).val.app V g)) =
            ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).unit.app
              (SheafOfModules.changeOfRingsPresheaf.{u, u, u} t (I G))).app
                ((Opens.map f.base).op.obj V)
                ((1 : B.obj.obj ((Opens.map f.base).op.obj V)) ⊗ₜ[
                  (IA).obj.obj ((Opens.map f.base).op.obj V),
                  (t.hom.app ((Opens.map f.base).op.obj V)).hom]
                  (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                    (Opens.map f.base) AddCommGrpCat.{u} (𝓙 X) (𝓙 U)).unit.app
                      ((SheafOfModules.toSheaf (𝓡 A)).obj G)).hom.app V g))) := by
  classical
  let F := inverseFunctor f.base A
  let E := extensionFunctor t
  let P := F ⋙ E
  let Q := F ⋙ SheafOfModules.restrictScalars (𝓻 t₀)
  let J := S ⋙ inverseFunctor f.base X.sheaf
  let j : Q ≅ J := NatIso.ofComponents (inverseRestrictIso f) (by
    intro G G' a
    ext W m
    rfl)
  obtain ⟨e, he, hu⟩ := SheafOfModules.sheafTensorPushoutCancellation r₀ t₀ b t hpush
  let c : P ⋙ SheafOfModules.restrictScalars (𝓻 b) ≅ Q ⋙ extensionFunctor r₀ :=
    NatIso.ofComponents (fun G ↦ e (F.obj G)) (fun a ↦ he _ _ (F.map a))
  let κ : P ⋙ SheafOfModules.restrictScalars (𝓻 b) ≅ S ⋙ tensorPullback f :=
    c ≪≫ Functor.isoWhiskerRight j (extensionFunctor r₀)
  refine ⟨P, fun _ ↦ rfl, κ, ?_, ?_⟩
  · intro G G' a
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  · intro G V g
    let W := (Opens.map f.base).op.obj V
    change (e (I G)).inv.val.app W
      (((extensionFunctor r₀).map (inverseRestrictIso f G).inv).val.app W
        (((adj₀).unit.app ((S).obj G)).val.app V g)) = _
    have hv := Classical.choose_spec (exists_tensorPullbackAdjunction f) ((S).obj G) V g
    refine (congrArg (fun x ↦ (e (I G)).inv.val.app W
      (((extensionFunctor r₀).map (inverseRestrictIso f G).inv).val.app W x)) hv).trans ?_
    let m := ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map f.base) AddCommGrpCat.{u} (𝓙 X) (𝓙 U)).unit.app
        ((SheafOfModules.toSheaf (𝓡 A)).obj G)).hom.app V g
    have hθ := extensionFunctor_unit r₀ (inverseRestrictIso f G).inv W
      ((1 : U.sheaf.obj.obj W) ⊗ₜ[
        (TopCat.Sheaf.inverseImageRing f.base X.sheaf).obj.obj W,
        ((r₀).hom.app W).hom] m)
    exact (congrArg (fun x ↦ (e (I G)).inv.val.app W x) hθ).trans (hu (I G) W m)

end
end AlgebraicGeometry.Scheme.Modules
