/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import WeilConjectures.AlgebraicGeometry.AffineModuleTensorCounitLinear
import WeilConjectures.AlgebraicGeometry.AffineModuleTensorExtensionEpi
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsAdjunction
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
/-! # Affine module tensor CoherenceComparisons

Source: Stacks Project, Morphisms, Lemma 01SB.
(blueprint: lem-weil-pbc-affine-module-tensor-counit-factor).
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

local instance instHasLeftKanExtension_affineModuleTensorCounitFactor
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

/-- The pullback counit factors through scalar extension; its comparison map is epic.
Source: Stacks Project, Morphisms, Lemma 01SB, construction of h and elucidation.
(blueprint: lem-weil-pbc-affine-module-tensor-counit-factor).

Proof: Identify P(RF) restricted to O_U with f^* S(RF) using κ. The counit
on a local tensor c tensor s evaluates to c s. To justify this identification
for the supplied κ, use hP on pullback-unit sections and the canonical unit
formula of adj₀. These sections generate inverse-image modules locally; after
scalar extension their O_U multiples generate P(RF) locally. Thus the hP
identification extends to all sections, and the adjunction triangle gives
the stated counit evaluation. The B-action is compatible with
the action on F through ε: the inverse-image ring counit evaluates the A factor,
and t ε = e gives exactly this evaluation. Check this first on products of pure
tensors, where both expressions are c c' a s, and extend additively and locally
through sheafification. Thus the counit is B-linear and the tensor universal
property along ε gives the asserted map from H(RF). The hH tensor-unit formula
then gives its composite with γ as the original counit. Finally γ is epic:
its image contains every sheafification section 1 tensor p, after identifying
via κ. Every tensor c tensor p is c times such a section, so these generate
locally. This proves local surjectivity and hence epimorphy of module sheaves.
No quasi-coherence or affineness is needed; zero rings and empty opens obey
exactly the same balanced tensor identities and local-generation argument. -/
theorem affine_module_tensor_counitFactor
    (B : U.toTopCat.Sheaf CommRingCat.{u}) (b : U.sheaf ⟶ B) (t : IA ⟶ B)
    (ε : B ⟶ U.sheaf) (hpush : IsPushout r₀ t₀ b t)
    (hb : b ≫ ε = 𝟙 U.sheaf) (ht : t ≫ ε = e₀)
    (P : SheafOfModules.{u} (𝓡 A) ⥤ SheafOfModules.{u} (𝓡 B))
        (pobj : ∀ G, P.obj G = SheafOfModules.changeOfRings.{u, u, u} t (I G))
        (κ : P ⋙ SheafOfModules.restrictScalars (𝓻 b) ≅ S ⋙ tensorPullback f)
    (H : SheafOfModules.{u} (𝓡 A) ⥤ U.Modules)
          (hobj : ∀ G, H.obj G = SheafOfModules.changeOfRings.{u, u, u} ε (P.obj G))
          (γ : S ⋙ tensorPullback f ⟶ H)
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
                      ((SheafOfModules.toSheaf (𝓡 A)).obj G)).hom.app V g))))
    (hH :
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
                  ((1 : U.sheaf.obj.obj W) ⊗ₜ[B.obj.obj W,(ε.hom.app W).hom] p))) :
    ∀ F : U.Modules,
      (∃ a : H.obj ((R).obj F) ⟶ F,
        γ.app ((R).obj F) ≫ a = (adj₀).counit.app F) ∧ Epi (γ.app ((R).obj F)) := by
  classical
  intro F
  let G := (R).obj F
  obtain ⟨δ, hδ⟩ := affine_module_tensor_counitLinear f B b t ε hpush hb ht P pobj κ hP F
  obtain ⟨E, q, adj, he⟩ :=
    SheafOfModules.exists_changeOfRingsAdjunction U.toTopCat B U.sheaf ε
  let a' : SheafOfModules.changeOfRings.{u, u, u} ε (P.obj G) ⟶ F :=
    eqToHom (q (P.obj G)).symm ≫ (adj.homEquiv (P.obj G) F).symm δ
  have ha (W : (Opens U)ᵒᵖ) (p : (P.obj G).val.obj W) :
      a'.val.app W
        (((PresheafOfModules.sheafificationAdjunction (𝟙 U.ringCatSheaf.obj)).unit.app
          (SheafOfModules.changeOfRingsPresheaf.{u, u, u} ε (P.obj G))).app W
            ((1 : U.sheaf.obj.obj W) ⊗ₜ[B.obj.obj W,(ε.hom.app W).hom] p)) =
        δ.val.app W p := by
    have h := he (P.obj G) F a' W p
    have hh : eqToHom (q (P.obj G)) ≫ a' =
        (adj.homEquiv (P.obj G) F).symm δ := by simp [a']
    exact h.symm.trans (congrArg (fun a ↦ a.val.app W p)
      ((congrArg (adj.homEquiv (P.obj G) F) hh).trans
        ((adj.homEquiv (P.obj G) F).apply_symm_apply δ)))
  let a : H.obj G ⟶ F := eqToHom (hobj G) ≫ a'
  refine ⟨⟨a, ?_⟩, ?_⟩
  · apply (cancel_epi (κ.hom.app G)).mp
    ext W p
    change a'.val.app W
      (((eqToHom (hobj G)).val.app W)
        ((γ.app G).val.app W ((κ.hom.app G).val.app W p))) = _
    exact (congrArg (a'.val.app W) (hH.2 G W p)).trans ((ha W p).trans (hδ W p))
  · exact affine_module_tensor_extension_epi f B b ε P κ H hobj γ hH.2 G

end
end AlgebraicGeometry.Scheme.Modules
