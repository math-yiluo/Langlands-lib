/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import WeilConjectures.AlgebraicGeometry.AffineModuleTensorBaseChange
import WeilConjectures.AlgebraicGeometry.AffineModuleTensorExtensionUnit
import WeilConjectures.AlgebraicGeometry.AffineModuleTensorCoherenceComparisons

/-! # Tensor construction for affine module correspondence

Source: Stacks Project, Morphisms, Lemma 01SB.
(blueprint: lem-weil-pbc-affine-module-tensor-construction).
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

local instance instHasLeftKanExtension_affineModuleTensorConstruction
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
set_option hygiene false in
local notation "qU" => SheafOfModules.isQuasicoherent U.ringCatSheaf
set_option hygiene false in
local notation "qA" => SheafOfModules.isQuasicoherent (𝓡 A)

/-- The tensor pushout, its extension-of-scalars functors, and the canonical comparison maps.
This assertion constructs the maps; it does not assert that they are isomorphisms.
Source: Stacks Project, Morphisms, Lemma 01SB, construction of h and elucidation.
(blueprint: lem-weil-pbc-affine-module-tensor-construction).

Proof:
1. Take the pushout of the inverse-image structure map and the inverse-image algebra map
   in commutative ring sheaves. The inverse-image counit and structure map commute, so
   the pushout universal property supplies ε with the two stated equations.
2. Extend inverse-image modules along t. Functoriality of inverse image and change of
   rings gives P and its map formula. Associativity of scalar extension identifies its
   underlying structure-sheaf module with tensor pullback; on the adjunction unit the
   comparison sends g to the sheafification of 1 tensor η(g). This fixes κ.
3. Extend P along ε to define H. The scalar-extension unit, conjugated by κ, defines γ.
   Its formula is the sheafification of 1 tensor p and is natural by functoriality.
4. The direct-image algebra is quasi-coherent by affine relative Spec. Scalar restriction,
   quasi-coherence of pullback, and change of rings between quasi-coherent algebras show
   that H carries quasi-coherent modules to quasi-coherent modules.
5. The pullback counit is linear over the pulled-back algebra: on tensor generators
   (b tensor a)(b' tensor s) maps to bb'as, the product of ε(b tensor a) and b's.
   Thus it factors through extension along ε to give α, naturally in F. The unit followed
   by γ is algebra-linear by the same generator computation, and gives β. The tensor
   universal property and the adjunction give the two displayed comparison equations.
-/
theorem affine_module_tensor_construction [IsAffineHom f] :
    ∃ (B : U.toTopCat.Sheaf CommRingCat.{u})
      (b : U.sheaf ⟶ B) (t : IA ⟶ B) (ε : B ⟶ U.sheaf),
      IsPushout r₀ t₀ b t ∧ b ≫ ε = 𝟙 U.sheaf ∧ t ≫ ε = e₀ ∧
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
                      ((SheafOfModules.toSheaf (𝓡 A)).obj G)).hom.app V g))) ∧
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
                  ((1 : U.sheaf.obj.obj W) ⊗ₜ[B.obj.obj W, (ε.hom.app W).hom] p)) ∧
          (∀ G : SheafOfModules.{u} (𝓡 A),
            G.IsQuasicoherent → (H.obj G).IsQuasicoherent) ∧
          ∃ (α : R ⋙ H ⟶ 𝟭 U.Modules) (β : 𝟭 (SheafOfModules.{u} (𝓡 A)) ⟶ H ⋙ R),
            (∀ F : U.Modules, γ.app ((R).obj F) ≫ α.app F = (adj₀).counit.app F) ∧
            (∀ G : SheafOfModules.{u} (𝓡 A),
              (S).map (β.app G) = ((adj₀).homEquiv ((S).obj G) (H.obj G)) (γ.app G)) := by
  classical
  have hc : r₀ = t₀ ≫ e₀ := by
    let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map f.base) CommRingCat.{u} (𝓙 X) (𝓙 U)
    simpa [tensorPullbackRingMap, TopCat.Sheaf.inverseImageConstruction] using
      adj.homEquiv_naturality_left_symm ρ (𝟙 A)
  have : HasPushout r₀ t₀ := inferInstance
  let B : U.toTopCat.Sheaf CommRingCat.{u} := pushout r₀ t₀
  let b : U.sheaf ⟶ B := pushout.inl r₀ t₀
  let t : IA ⟶ B := pushout.inr r₀ t₀
  let ε : B ⟶ U.sheaf := pushout.desc (𝟙 U.sheaf) e₀ (by simpa using hc)
  have hp : IsPushout r₀ t₀ b t := IsPushout.of_hasPushout r₀ t₀
  have hb : b ≫ ε = 𝟙 U.sheaf := pushout.inl_desc _ _ _
  have ht : t ≫ ε = e₀ := pushout.inr_desc _ _ _
  refine ⟨B, b, t, ε, hp, hb, ht, ?_⟩
  -- Assemble each layer before introducing the next to keep elimination goals small.
  have hbase :=
    affine_module_tensor_baseChange (U := U) (X := X) f B b t hp
  rcases hbase with ⟨P, pobj, κ, hmapP, hunitP⟩
  refine ⟨P, pobj, κ, hmapP, hunitP, ?_⟩
  have hext :=
    affine_module_tensor_extensionUnit (U := U) (X := X) f B b t ε hb P pobj κ
  rcases hext with ⟨H, hobj, γ, hmapH, hunitH⟩
  refine ⟨H, hobj, γ, hmapH, hunitH, ?_⟩
  exact affine_module_tensor_coherenceComparisons (U := U) (X := X) f B b t ε
    hp hb ht P pobj κ H hobj γ ⟨hmapP, hunitP⟩ ⟨hmapH, hunitH⟩

end
end AlgebraicGeometry.Scheme.Modules
