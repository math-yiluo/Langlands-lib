/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsAdjunction
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TopologicalPullback
/-! # Affine module tensor CoherenceComparisons

Source: Stacks Project, Morphisms, Lemma 01SB.
(blueprint: lem-weil-pbc-affine-module-tensor-unit-lift).
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
local notation "e₀" => (by
  have : ∀ (F : (Opens X)ᵒᵖ ⥤ CommRingCat.{u}),
      (Opens.map f.base).op.HasLeftKanExtension F := fun F ↦ by
    have : (Opens.map f.base).op.HasPointwiseLeftKanExtension F := fun _ ↦ inferInstance
    exact Functor.HasLeftKanExtension.mk _
      (Functor.pointwiseLeftKanExtensionUnit (Opens.map f.base).op F)
  exact ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f.base) CommRingCat.{u} (𝓙 X) (𝓙 U)).homEquiv A U.sheaf).symm (𝟙 A))
set_option hygiene false in
local notation "adj₀" => Classical.choose (exists_tensorPullbackAdjunction f)
set_option hygiene false in
local notation "qU" => SheafOfModules.isQuasicoherent U.ringCatSheaf
set_option hygiene false in
local notation "qA" => SheafOfModules.isQuasicoherent (𝓡 A)

private theorem tensor_changeOfRings_adjunct
    (Y : TopCat.{u}) (B C : Y.Sheaf CommRingCat.{u}) (φ : B ⟶ C)
    (M : SheafOfModules.{u} (𝓡 B)) (N : SheafOfModules.{u} (𝓡 C))
    (k : SheafOfModules.changeOfRings.{u, u, u} φ M ⟶ N) :
    ∃ q : M ⟶ (SheafOfModules.restrictScalars (𝓻 φ)).obj N,
      ∀ (W : (TopologicalSpace.Opens Y)ᵒᵖ) (m : M.val.obj W),
        q.val.app W m = k.val.app W
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 C).obj)).unit.app
            (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ M)).app W
              ((1 : C.obj.obj W) ⊗ₜ[B.obj.obj W,(φ.hom.app W).hom] m)) := by
  obtain ⟨E, hE, adj, he⟩ := SheafOfModules.exists_changeOfRingsAdjunction Y B C φ
  exact ⟨adj.homEquiv M N (eqToHom (hE M) ≫ k), he M N k⟩

private theorem tensor_ring_counit_unit_section
    [∀ (F : (Opens X)ᵒᵖ ⥤ CommRingCat.{u}),
      (Opens.map f.base).op.HasLeftKanExtension F]
    (V : (Opens X)ᵒᵖ) (r : (A).obj.obj V) :
    (show IA ⟶ U.sheaf from e₀).hom.app ((Opens.map f.base).op.obj V)
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (Opens.map f.base) CommRingCat.{u} (𝓙 X) (𝓙 U)).unit.app A).hom.app V r) = r := by
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f.base) CommRingCat.{u} (𝓙 X) (𝓙 U)
  have h := (adj.homEquiv_unit A U.sheaf
    ((adj.homEquiv A U.sheaf).symm (𝟙 A))).symm.trans
      ((adj.homEquiv A U.sheaf).apply_symm_apply (𝟙 A))
  exact congrArg (fun a ↦ a.hom.app V r) h

/-- The adjoint of γ is linear over the affine direct-image algebra, objectwise.
Source: Stacks Project, Morphisms, Lemma 01SB, construction of h and elucidation.
(blueprint: lem-weil-pbc-affine-module-tensor-unit-lift).

Proof: The adjoint of γ is the pullback unit followed by pushforward of γ.
Its component on a section g over V is γ applied to the pullback-unit section.
Apply κ inverse and the hP unit formula to identify this section with the
sheafification of 1 tensor η(g). Apply the hH formula to obtain the second
scalar-extension unit. For a section a of A(V), η(a g) is η(a) η(g), by
linearity of inverse-image modules. The balanced relation first moves η(a)
onto the B tensor factor through t, and then across the ε extension. Since
t ε = e, and the inverse-image ring counit composed with its unit is the
identity, the result is a times the section computed for g in R(HG).
Additivity and compatibility with restrictions already hold for the adjoint.
These equalities therefore equip the same component maps with A-linearity,
producing the desired morphism a. Forgetting A scalars gives exactly the
original adjoint. No affineness or quasi-coherence is used, and the calculation
still holds for the zero ring, zero module and empty opens. -/
theorem affine_module_tensor_unitLift
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
    ∀ G : SheafOfModules.{u} (𝓡 A),
      ∃ a : G ⟶ (R).obj (H.obj G),
        (S).map a = ((adj₀).homEquiv ((S).obj G) (H.obj G)) (γ.app G) := by
  classical
  have : ∀ (F : (Opens X)ᵒᵖ ⥤ CommRingCat.{u}),
      (Opens.map f.base).op.HasLeftKanExtension F := fun F ↦ by
    have : (Opens.map f.base).op.HasPointwiseLeftKanExtension F := fun _ ↦ inferInstance
    exact Functor.HasLeftKanExtension.mk _
      (Functor.pointwiseLeftKanExtensionUnit (Opens.map f.base).op F)
  let : (Opens.map f.base).IsContinuous (𝓙 X) (𝓙 U.toTopCat) :=
    inferInstanceAs ((Opens.map f.base).IsContinuous (𝓙 X) (𝓙 U))
  have _ := hpush
  have _ := hb
  intro G
  -- The second extension unit is B-linear and agrees with γ after κ.
  have hzData := tensor_changeOfRings_adjunct U.toTopCat B U.sheaf ε
    (P.obj G) (H.obj G) (eqToHom (hobj G).symm)
  let z := hzData.choose
  have hz₀ := hzData.choose_spec
  have hz (W : (Opens U)ᵒᵖ) (p : (P.obj G).val.obj W) :
      z.val.app W p = (γ.app G).val.app W ((κ.hom.app G).val.app W p) := by
    refine (hz₀ W p).trans ((congrArg ((eqToHom (hobj G).symm).val.app W)
      (hH.2 G W p).symm).trans ?_)
    change ((eqToHom (hobj G) ≫ eqToHom (hobj G).symm).val.app W)
      ((γ.app G).val.app W ((κ.hom.app G).val.app W p)) = _
    simp only [eqToHom_trans, eqToHom_refl]
    rfl
  -- Composing the two tensor units gives an IA-linear map.
  have hqData := tensor_changeOfRings_adjunct U.toTopCat IA B t (I G)
    ((SheafOfModules.restrictScalars (𝓻 ε)).obj (H.obj G))
    (eqToHom (pobj G).symm ≫ z)
  let q := hqData.choose
  have hunit := hqData.choose_spec
  let adjAb := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f.base) AddCommGrpCat.{u} (𝓙 X) (𝓙 U)
  let d := (adj₀).homEquiv ((S).obj G) (H.obj G) (γ.app G)
  -- The prescribed unit formulas identify its adjunct with the original adjunct.
  have hd (V : (Opens X)ᵒᵖ) (g : G.val.obj V) :
      d.val.app V g = q.val.app ((Opens.map f.base).op.obj V)
        ((adjAb.unit.app ((SheafOfModules.toSheaf (𝓡 A)).obj G)).hom.app V g) := by
    let W := (Opens.map f.base).op.obj V
    have hq₀ := hunit W
      ((adjAb.unit.app ((SheafOfModules.toSheaf (𝓡 A)).obj G)).hom.app V g)
    symm
    refine hq₀.trans ((congrArg ((eqToHom (pobj G).symm ≫ z).val.app W)
      (hP.2 G V g).symm).trans ?_)
    change z.val.app W
      ((eqToHom (pobj G) ≫ eqToHom (pobj G).symm).val.app W
        ((κ.inv.app G).val.app W (((adj₀).unit.app ((S).obj G)).val.app V g))) = _
    simp only [eqToHom_trans, eqToHom_refl]
    refine (hz W _).trans ?_
    change (γ.app G).val.app W
      ((κ.inv.app G ≫ κ.hom.app G).val.app W
        (((adj₀).unit.app ((S).obj G)).val.app V g)) = _
    have hk := congrArg (fun a ↦ a.val.app W
      (((adj₀).unit.app ((S).obj G)).val.app V g)) (κ.inv_hom_id_app G)
    refine (congrArg ((γ.app G).val.app W) hk).trans ?_
    exact (congrArg (fun a ↦ a.val.app V g)
      ((adj₀).homEquiv_unit ((S).obj G) (H.obj G) (γ.app G))).symm
  -- Semilinearity of inverse image and the ring triangle give A-linearity.
  have hscalar (V : (Opens X)ᵒᵖ) (r : (A).obj.obj V) (g : G.val.obj V) :
      d.val.app V (r • g) =
        @SMul.smul _ _ (((R).obj (H.obj G)).val.obj V).isModule.toSMul r
          (d.val.app V g) := by
    refine (hd V (r • g)).trans ?_
    refine (congrArg (q.val.app ((Opens.map f.base).op.obj V))
      ((Classical.choose_spec
        (TopCat.Sheaf.exists_inverseImageModuleInstances f.base A G)).2 V r g)).trans ?_
    refine ((q.val.app ((Opens.map f.base).op.obj V)).hom.map_smul _ _).trans ?_
    let adjRing := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map f.base) CommRingCat.{u} (𝓙 X) (𝓙 U)
    have hr : ε.hom.app ((Opens.map f.base).op.obj V)
        (t.hom.app ((Opens.map f.base).op.obj V)
          ((adjRing.unit.app A).hom.app V r)) = r := by
      have he := congrArg (fun a ↦ a.hom.app ((Opens.map f.base).op.obj V)
        ((adjRing.unit.app A).hom.app V r)) ht
      exact he.trans (tensor_ring_counit_unit_section f V r)
    change @SMul.smul _ _
      ((H.obj G).val.obj ((Opens.map f.base).op.obj V)).isModule.toSMul
      (ε.hom.app ((Opens.map f.base).op.obj V)
        (t.hom.app ((Opens.map f.base).op.obj V)
          ((adjRing.unit.app A).hom.app V r))) _ =
      @SMul.smul _ _
        ((H.obj G).val.obj ((Opens.map f.base).op.obj V)).isModule.toSMul r _
    exact congrArg₂ (fun r p ↦ @SMul.smul _ _
      ((H.obj G).val.obj ((Opens.map f.base).op.obj V)).isModule.toSMul r p)
      hr (hd V g).symm
  let a : G ⟶ (R).obj (H.obj G) :=
    ⟨PresheafOfModules.homMk
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map d.val) hscalar⟩
  refine ⟨a, ?_⟩
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  exact LinearMap.ext fun _ ↦ rfl

end
end AlgebraicGeometry.Scheme.Modules
