/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import WeilConjectures.AlgebraicGeometry.AffineModuleTensorCounitSmul
/-! # Linearity of the affine tensor counit

Source: Stacks Project, Morphisms, Lemma 01SB.
(blueprint: lem-weil-pbc-affine-module-tensor-counit-linear).
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

local instance instHasLeftKanExtension_affineModuleTensorCounitLinear
    : ∀ (F : (Opens X)ᵒᵖ ⥤ CommRingCat.{u}),
    (Opens.map f.base).op.HasLeftKanExtension F := fun F ↦ by
  have : (Opens.map f.base).op.HasPointwiseLeftKanExtension F := fun _ ↦ inferInstance
  exact Functor.HasLeftKanExtension.mk _
    (Functor.pointwiseLeftKanExtensionUnit (Opens.map f.base).op F)

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
/-- The counit transported by κ is B-linear when F carries its B-action through ε.
Source: Stacks Project, Morphisms, Lemma 01SB, construction of h and elucidation.
(blueprint: lem-weil-pbc-affine-module-tensor-counit-linear).

Proof: Let q be the O_U-linear composite κ followed by the pullback counit. By the
canonical pullback unit formula and hP, q on the sheafification of 1 tensor η(g) is the
section g of F over the inverse image of its domain: this is the adjunction triangle.
The underlying inverse-image counit is IA-linear for the action on F through e, by
the inverse-image module adjunction. Hence tensor evaluation sends c tensor s to
ε(c) times the inverse-image counit of s; t ε = e makes this balanced over IA. It
commutes with restriction and induces a B-linear map δ after sheafification. On the
above unit sections δ agrees with q. Inverse-image unit sections locally generate
the inverse-image sheaf, and their O_U multiples locally generate the restriction
of P along b: the pushout identifies it with O_U tensor_{f⁻¹ O_X} I(RF). Therefore
O_U-linearity extends the equality from those sections to all sections, giving the
asserted formula for δ. Its formula determines δ uniquely. No affineness or
quasi-coherence is used. Empty opens and zero rings obey the same balanced identities. -/
theorem affine_module_tensor_counitLinear
    (B : U.toTopCat.Sheaf CommRingCat.{u}) (b : U.sheaf ⟶ B) (t : IA ⟶ B)
    (ε : B ⟶ U.sheaf) (hpush : IsPushout r₀ t₀ b t)
    (hb : b ≫ ε = 𝟙 U.sheaf) (ht : t ≫ ε = e₀)
    (P : SheafOfModules.{u} (𝓡 A) ⥤ SheafOfModules.{u} (𝓡 B))
        (pobj : ∀ G, P.obj G = SheafOfModules.changeOfRings.{u, u, u} t (I G))
        (κ : P ⋙ SheafOfModules.restrictScalars (𝓻 b) ≅ S ⋙ tensorPullback f)
    (hP :
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
                ((1 : B.obj.obj ((Opens.map f.base).op.obj V))
                  ⊗ₜ[(IA).obj.obj ((Opens.map f.base).op.obj V),(t.hom.app
                    ((Opens.map f.base).op.obj V)).hom]
                  (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                    (Opens.map f.base) AddCommGrpCat.{u} (𝓙 X) (𝓙 U)).unit.app
                      ((SheafOfModules.toSheaf (𝓡 A)).obj G)).hom.app V g)))) :
    ∀ F : U.Modules,
      ∃ δ : P.obj ((R).obj F) ⟶ (SheafOfModules.restrictScalars (𝓻 ε)).obj F,
        ∀ (W : (Opens U)ᵒᵖ) (p : (P.obj ((R).obj F)).val.obj W),
          δ.val.app W p =
            ((adj₀).counit.app F).val.app W ((κ.hom.app ((R).obj F)).val.app W p) := by
  intro F
  let q := (κ.hom.app ((R).obj F)).val ≫ ((adj₀).counit.app F).val
  let φ : (P.obj ((R).obj F)).val.presheaf ⟶
      ((SheafOfModules.restrictScalars (𝓻 ε)).obj F).val.presheaf :=
    (PresheafOfModules.toPresheaf U.ringCatSheaf.obj).map q
  refine ⟨⟨PresheafOfModules.homMk φ ?_⟩, ?_⟩
  · intro W c p
    change ((adj₀).counit.app F).val.app W
        ((κ.hom.app ((R).obj F)).val.app W (c • p)) =
      (ε.hom.app W c) •
        ((adj₀).counit.app F).val.app W ((κ.hom.app ((R).obj F)).val.app W p)
    exact affine_module_tensor_counit_smul f B b t ε hpush hb ht P pobj κ hP F W c p
  · intro W p
    rfl

end
end AlgebraicGeometry.Scheme.Modules
