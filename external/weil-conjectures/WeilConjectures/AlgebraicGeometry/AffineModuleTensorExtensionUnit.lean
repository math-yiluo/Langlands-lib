/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct

/-! # Affine module tensor ExtensionUnit

Source: Stacks Project, Morphisms, Lemma 01SB.
(blueprint: lem-weil-pbc-affine-module-tensor-extension-unit).
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

/-- Extension along ε supplies a functor and its canonical tensor unit after κ.
Source: Stacks Project, Morphisms, Lemma 01SB, construction of h.
Proof: Use change of rings along ε on P objects and sheafify id tensor P(a) on morphisms.
The maps preserve identities and composition because tensor extension and sheafification
do. The scalar-extension adjunction unit sends p to the sheafification of 1 tensor p.
Compose this unit, after P, with κ inverse to define γ. Its naturality follows from
naturality of the unit and κ. Composing with κ cancels κ inverse, giving the section
formula. The equation bε=1 makes the unit O_U-linear; no affineness or
quasi-coherence is needed; the zero ring and zero module satisfy the same construction.
(blueprint: lem-weil-pbc-affine-module-tensor-extension-unit). -/
theorem affine_module_tensor_extensionUnit
    (B : U.toTopCat.Sheaf CommRingCat.{u}) (b : U.sheaf ⟶ B) (t : IA ⟶ B)
    (ε : B ⟶ U.sheaf) (hb : b ≫ ε = 𝟙 U.sheaf)
    (P : SheafOfModules.{u} (𝓡 A) ⥤ SheafOfModules.{u} (𝓡 B))
        (pobj : ∀ G, P.obj G = SheafOfModules.changeOfRings.{u, u, u} t (I G))
        (κ : P ⋙ SheafOfModules.restrictScalars (𝓻 b) ≅ S ⋙ tensorPullback f) :
        ∃ (H : SheafOfModules.{u} (𝓡 A) ⥤ U.Modules)
          (hobj : ∀ G, H.obj G = SheafOfModules.changeOfRings.{u, u, u} ε (P.obj G))
          (γ : S ⋙ tensorPullback f ⟶ H),
          (∀ (G G' : SheafOfModules.{u} (𝓡 A)) (a : G ⟶ G'),
            H.map a = eqToHom (hobj G) ≫
              SheafOfModules.changeOfRingsHom.{u, u, u} ε (P.obj G) (P.map a) ≫
              eqToHom (hobj G').symm) ∧
          (∀ (G : SheafOfModules.{u} (𝓡 A)) (W : (Opens U)ᵒᵖ)
              (p : (P.obj G).val.obj W),
            ((eqToHom (hobj G)).val.app W)
              ((γ.app G).val.app W ((κ.hom.app G).val.app W p)) =
              ((PresheafOfModules.sheafificationAdjunction (𝟙 U.ringCatSheaf.obj)).unit.app
                (SheafOfModules.changeOfRingsPresheaf.{u, u, u} ε (P.obj G))).app W
                  ((1 : U.sheaf.obj.obj W) ⊗ₜ[B.obj.obj W, (ε.hom.app W).hom] p)) := by
  have := pobj
  let T : SheafOfModules.{u} (𝓡 B) ⥤ _root_.PresheafOfModules.{u} U.ringCatSheaf.obj :=
    { obj := fun M ↦ SheafOfModules.changeOfRingsPresheaf.{u, u, u} ε M
      map := fun {M N} a ↦
        show SheafOfModules.changeOfRingsPresheaf.{u, u, u} ε M ⟶
          SheafOfModules.changeOfRingsPresheaf.{u, u, u} ε N from
        { app := fun W ↦ (ModuleCat.extendScalars (ε.hom.app W).hom).map (a.val.app W)
          naturality := SheafOfModules.changeOfRingsHom_naturality.{u, u, u} ε _ a }
      map_id := by
        intro M
        apply PresheafOfModules.hom_ext
        intro W
        exact (ModuleCat.extendScalars (ε.hom.app W).hom).map_id _
      map_comp := by
        intro M N L a c
        apply PresheafOfModules.hom_ext
        intro W
        exact (ModuleCat.extendScalars (ε.hom.app W).hom).map_comp _ _ }
  let F := PresheafOfModules.sheafification (𝟙 U.ringCatSheaf.obj)
  let H := P ⋙ T ⋙ F
  let q (M : SheafOfModules.{u} (𝓡 B)) :
      ((SheafOfModules.restrictScalars (𝓻 b)).obj M).val ⟶ T.obj M := by
    refine { app := ?_, naturality := ?_ }
    · intro W
      refine ModuleCat.ofHom
        (X := ((SheafOfModules.restrictScalars (𝓻 b)).obj M).val.obj W)
        (Y := (T.obj M).obj W)
        { toFun := fun m ↦ (1 : U.sheaf.obj.obj W) ⊗ₜ[B.obj.obj W, (ε.hom.app W).hom] m
          map_add' := by intros; exact TensorProduct.tmul_add _ _ _
          map_smul' := ?_ }
      intro r m
      let : Module (B.obj.obj W) (U.sheaf.obj.obj W) :=
        Module.compHom (U.sheaf.obj.obj W) (ε.hom.app W).hom
      change (1 : U.sheaf.obj.obj W) ⊗ₜ[B.obj.obj W, (ε.hom.app W).hom]
        (b.hom.app W r • (show M.val.obj W from m)) = (show U.sheaf.obj.obj W from r) •
          ((1 : U.sheaf.obj.obj W) ⊗ₜ[B.obj.obj W, (ε.hom.app W).hom] (show M.val.obj W from m))
      have hr : ε.hom.app W (b.hom.app W r) = r :=
        ConcreteCategory.congr_hom (congrArg (fun a ↦ a.hom.app W) hb)
          (show U.sheaf.obj.obj W from r)
      change (1 : U.sheaf.obj.obj W) ⊗ₜ[B.obj.obj W] (b.hom.app W r • (show M.val.obj W from m)) = _
      rw [TensorProduct.tmul_smul]
      change (ε.hom.app W (b.hom.app W r) * 1) ⊗ₜ[B.obj.obj W] (show M.val.obj W from m) = _
      rw [hr, mul_one]
      simpa only [mul_one] using
        (ModuleCat.ExtendScalars.smul_tmul (ε.hom.app W).hom
          (show U.sheaf.obj.obj W from r) 1 (show M.val.obj W from m)).symm
    · intro V W i
      ext m
      symm
      change SheafOfModules.changeOfRingsMap ε M i
        ((1 : U.sheaf.obj.obj V) ⊗ₜ[B.obj.obj V, (ε.hom.app V).hom] m) = _
      refine (Classical.choose_spec
        (SheafOfModules.exists_changeOfRingsMap ε M i) 1 m).trans ?_
      simp only [map_one]
      rfl
  let δ : P ⋙ SheafOfModules.restrictScalars (𝓻 b) ⟶ H :=
    { app := fun G ↦ ⟨q (P.obj G) ≫
        (PresheafOfModules.sheafificationAdjunction (𝟙 U.ringCatSheaf.obj)).unit.app
          (T.obj (P.obj G))⟩
      naturality := by
        intro G G' a
        apply SheafOfModules.hom_ext
        change ((SheafOfModules.restrictScalars (𝓻 b)).map (P.map a)).val ≫
          (q (P.obj G') ≫
            (PresheafOfModules.sheafificationAdjunction (𝟙 U.ringCatSheaf.obj)).unit.app
              (T.obj (P.obj G'))) =
          (q (P.obj G) ≫
            (PresheafOfModules.sheafificationAdjunction (𝟙 U.ringCatSheaf.obj)).unit.app
              (T.obj (P.obj G))) ≫ (F.map (T.map (P.map a))).val
        have hq : ((SheafOfModules.restrictScalars (𝓻 b)).map (P.map a)).val ≫
            q (P.obj G') = q (P.obj G) ≫ T.map (P.map a) := by
          ext W m
          change (1 : U.sheaf.obj.obj W) ⊗ₜ[B.obj.obj W, (ε.hom.app W).hom]
            ((P.map a).val.app W m) =
            (ModuleCat.extendScalars (ε.hom.app W).hom).map ((P.map a).val.app W)
              ((1 : U.sheaf.obj.obj W) ⊗ₜ[B.obj.obj W, (ε.hom.app W).hom] m)
          erw [ModuleCat.ExtendScalars.map_tmul]
          rfl
        rw [← Category.assoc, hq, Category.assoc]
        have hn := (PresheafOfModules.sheafificationAdjunction
          (𝟙 U.ringCatSheaf.obj)).unit.naturality (T.map (P.map a))
        change T.map (P.map a) ≫
          (PresheafOfModules.sheafificationAdjunction (𝟙 U.ringCatSheaf.obj)).unit.app
            (T.obj (P.obj G')) =
          (PresheafOfModules.sheafificationAdjunction (𝟙 U.ringCatSheaf.obj)).unit.app
            (T.obj (P.obj G)) ≫ (F.map (T.map (P.map a))).val at hn
        rw [hn, Category.assoc] }
  refine ⟨H, fun _ ↦ rfl, κ.inv ≫ δ, ?_, ?_⟩
  · intro G G' a
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  · intro G W p
    change (δ.app G).val.app W ((κ.inv.app G).val.app W
      ((κ.hom.app G).val.app W p)) = _
    have hk : (κ.inv.app G).val.app W ((κ.hom.app G).val.app W p) = p :=
      congrArg (fun a ↦ a.val.app W p) (κ.hom_inv_id_app G)
    rw [hk]
    change ((PresheafOfModules.sheafificationAdjunction
      (𝟙 U.ringCatSheaf.obj)).unit.app (T.obj (P.obj G))).app W
        ((q (P.obj G)).app W p) = _
    rfl
end
end AlgebraicGeometry.Scheme.Modules
