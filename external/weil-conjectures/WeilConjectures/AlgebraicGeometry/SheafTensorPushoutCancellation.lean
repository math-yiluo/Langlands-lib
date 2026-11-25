/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import WeilConjectures.AlgebraicGeometry.SheafTensorPushoutComparisonIsIso
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Cancellation of tensor extension over a pushout of ring sheaves

Source: Stacks Project, Tag 01SB, tensor construction, and Tag 008A.
(blueprint: lem-weil-pbc-sheaf-tensor-pushout-cancellation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped ChangeOfRings

namespace SheafOfModules

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {T : TopCat.{u}} {D C A B : T.Sheaf CommRingCat.{u}}

set_option hygiene false in
local notation "𝓡" E =>
  (sheafCompose (Opens.grothendieckTopology T) (forget₂ CommRingCat.{u} RingCat.{u})).obj E
set_option hygiene false in
local notation "𝓻" a =>
  (sheafCompose (Opens.grothendieckTopology T) (forget₂ CommRingCat.{u} RingCat.{u})).map a
private def tensorUnit {R₁ R₂ : T.Sheaf CommRingCat.{u}} (α : R₁ ⟶ R₂)
    (M : SheafOfModules.{u} (𝓡 R₁)) :
    changeOfRingsPresheaf.{u, u, u} α M ⟶
      (PresheafOfModules.restrictScalars (𝟙 (𝓡 R₂).obj)).obj
        (changeOfRings.{u, u, u} α M).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 R₂).obj)).unit.app
    (changeOfRingsPresheaf.{u, u, u} α M)

private def comparisonSection (r : D ⟶ C) (s : D ⟶ A) (b : C ⟶ B) (t : A ⟶ B)
    (h : r ≫ b = s ≫ t) (M : SheafOfModules.{u} (𝓡 A)) (W : (Opens T)ᵒᵖ) :
    (changeOfRingsPresheaf.{u, u, u} r ((restrictScalars (𝓻 s)).obj M)).obj W ⟶
      (ModuleCat.restrictScalars (b.hom.app W).hom).obj
        ((changeOfRings.{u, u, u} t M).val.obj W) := by
  let N := (ModuleCat.restrictScalars (b.hom.app W).hom).obj
    ((changeOfRings.{u, u, u} t M).val.obj W)
  let g : ((restrictScalars (𝓻 s)).obj M).val.obj W ⟶
      (ModuleCat.restrictScalars (r.hom.app W).hom).obj N :=
    ModuleCat.ofHom
      (X := ((restrictScalars (𝓻 s)).obj M).val.obj W)
      (Y := (ModuleCat.restrictScalars (r.hom.app W).hom).obj N)
      { toFun := fun m ↦ (tensorUnit t M).app W
          ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (t.hom.app W).hom] m)
        map_add' := by
          intro m n
          rw [TensorProduct.tmul_add]
          exact ((tensorUnit t M).app W).hom.map_add _ _
        map_smul' := by
          intro d m
          change (tensorUnit t M).app W
            ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (t.hom.app W).hom]
              ((s.hom.app W d) • (show M.val.obj W from m))) =
            (b.hom.app W (r.hom.app W d)) • (show (changeOfRings.{u, u, u} t M).val.obj W from
              (tensorUnit t M).app W
                ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (t.hom.app W).hom] m))
          have hd : b.hom.app W (r.hom.app W d) = t.hom.app W (s.hom.app W d) :=
            ConcreteCategory.congr_hom
              (congrArg (fun f : D ⟶ B ↦ f.hom.app W) h) (show D.obj.obj W from d)
          rw [hd]
          let : Module (A.obj.obj W) (B.obj.obj W) :=
            Module.compHom (B.obj.obj W) (t.hom.app W).hom
          rw [TensorProduct.tmul_smul]
          change (tensorUnit t M).app W
            ((t.hom.app W (s.hom.app W d)) •
              ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (t.hom.app W).hom]
                (show M.val.obj W from m))) = _
          exact ((tensorUnit t M).app W).hom.map_smul _ _ }
  exact ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (r.hom.app W).hom g

private theorem comparisonSection_tmul
    (r : D ⟶ C) (s : D ⟶ A) (b : C ⟶ B) (t : A ⟶ B)
    (h : r ≫ b = s ≫ t) (M : SheafOfModules.{u} (𝓡 A))
    (W : (Opens T)ᵒᵖ) (c : C.obj.obj W) (m : M.val.obj W) :
    comparisonSection r s b t h M W
      (c ⊗ₜ[D.obj.obj W,(r.hom.app W).hom] m) =
    (tensorUnit t M).app W ((b.hom.app W c) ⊗ₜ[A.obj.obj W, (t.hom.app W).hom] m) := by
  let : Module (D.obj.obj W) (C.obj.obj W) :=
    Module.compHom (C.obj.obj W) (r.hom.app W).hom
  let N := (ModuleCat.restrictScalars (b.hom.app W).hom).obj
    ((changeOfRings.{u, u, u} t M).val.obj W)
  let : Module (D.obj.obj W) N := Module.compHom N (r.hom.app W).hom
  unfold comparisonSection
  erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply,
    TensorProduct.lift.tmul]
  change b.hom.app W c • (show (changeOfRings.{u, u, u} t M).val.obj W from
    (tensorUnit t M).app W ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (t.hom.app W).hom] m)) = _
  rw [← ((tensorUnit t M).app W).hom.map_smul]
  congr 1
  change (b.hom.app W c) •
    ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (t.hom.app W).hom] m) = _
  rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]

section

local instance localInst_SheafTensorPushoutCancellation_1
    (M : SheafOfModules.{u} (𝓡 D)) {U V : (Opens T)ᵒᵖ} (i : U ⟶ V) :
    Module (D.obj.obj V)
      ((ModuleCat.restrictScalars ((𝓡 D).obj.map i).hom).obj (M.val.obj V)) :=
  inferInstanceAs (Module (D.obj.obj V) (M.val.obj V))

private theorem tensorRestriction_tmul (r : D ⟶ C) (M : SheafOfModules.{u} (𝓡 D))
    {U V : (Opens T)ᵒᵖ} (i : U ⟶ V) (c : C.obj.obj U) (m : M.val.obj U) :
    changeOfRingsMap.{u, u, u} r M i
      (c ⊗ₜ[D.obj.obj U, (r.hom.app U).hom] m) =
      C.obj.map i c ⊗ₜ[D.obj.obj V, (r.hom.app V).hom] M.val.map i m :=
  Classical.choose_spec (exists_changeOfRingsMap.{u, u, u} r M i) c m

end

private def comparisonSeed (r : D ⟶ C) (s : D ⟶ A) (b : C ⟶ B) (t : A ⟶ B)
    (h : r ≫ b = s ≫ t) (M : SheafOfModules.{u} (𝓡 A)) :
    changeOfRingsPresheaf.{u, u, u} r ((restrictScalars (𝓻 s)).obj M) ⟶
      (PresheafOfModules.restrictScalars (𝟙 (𝓡 C).obj)).obj
        (((restrictScalars (𝓻 b)).obj (changeOfRings.{u, u, u} t M)).val) where
  app W := comparisonSection r s b t h M W
  naturality := by
    intro U V i
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change comparisonSection r s b t h M V
      (changeOfRingsMap.{u, u, u} r ((restrictScalars (𝓻 s)).obj M) i
        ((1 : C.obj.obj U) ⊗ₜ[D.obj.obj U, (r.hom.app U).hom] m)) =
      (changeOfRings.{u, u, u} t M).val.map i (comparisonSection r s b t h M U
        ((1 : C.obj.obj U) ⊗ₜ[D.obj.obj U, (r.hom.app U).hom] m))
    rw [tensorRestriction_tmul]
    simp only [map_one]
    rw [comparisonSection_tmul, comparisonSection_tmul]
    simp only [map_one]
    have hn := PresheafOfModules.naturality_apply (tensorUnit t M) i
      ((1 : B.obj.obj U) ⊗ₜ[A.obj.obj U, (t.hom.app U).hom]
        (show M.val.obj U from m))
    change (tensorUnit t M).app V (changeOfRingsMap.{u, u, u} t M i _) = _ at hn
    rw [tensorRestriction_tmul] at hn
    simp only [map_one] at hn
    exact hn

private def comparison (r : D ⟶ C) (s : D ⟶ A) (b : C ⟶ B) (t : A ⟶ B)
    (h : r ≫ b = s ≫ t) (M : SheafOfModules.{u} (𝓡 A)) :
    changeOfRings.{u, u, u} r ((restrictScalars (𝓻 s)).obj M) ⟶
      (restrictScalars (𝓻 b)).obj (changeOfRings.{u, u, u} t M) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 (𝓡 C).obj)).symm
    (comparisonSeed r s b t h M)

private theorem comparison_tmul
    (r : D ⟶ C) (s : D ⟶ A) (b : C ⟶ B) (t : A ⟶ B)
    (h : r ≫ b = s ≫ t) (M : SheafOfModules.{u} (𝓡 A))
    (W : (Opens T)ᵒᵖ) (c : C.obj.obj W) (m : M.val.obj W) :
    (comparison r s b t h M).val.app W
      ((tensorUnit r ((restrictScalars (𝓻 s)).obj M)).app W
        (c ⊗ₜ[D.obj.obj W,(r.hom.app W).hom] m)) =
      (tensorUnit t M).app W ((b.hom.app W c) ⊗ₜ[A.obj.obj W, (t.hom.app W).hom] m) := by
  have he := (PresheafOfModules.sheafificationHomEquiv (𝟙 (𝓡 C).obj)
    (P := changeOfRingsPresheaf.{u, u, u} r ((restrictScalars (𝓻 s)).obj M))
    (F := (restrictScalars (𝓻 b)).obj (changeOfRings.{u, u, u} t M))).apply_symm_apply
    (comparisonSeed r s b t h M)
  have hv := congrArg (fun f ↦ f.app W) he
  have hx := ConcreteCategory.congr_hom hv
    (c ⊗ₜ[D.obj.obj W,(r.hom.app W).hom]
      (show ((restrictScalars (𝓻 s)).obj M).val.obj W from m))
  change (comparison r s b t h M).val.app W
    ((tensorUnit r ((restrictScalars (𝓻 s)).obj M)).app W _) =
      comparisonSection r s b t h M W _ at hx
  exact hx.trans (comparisonSection_tmul r s b t h M W c m)

private theorem tensorHom_ext (r : D ⟶ C) (M : SheafOfModules.{u} (𝓡 D))
    {N : SheafOfModules.{u} (𝓡 C)} (f g : changeOfRings.{u, u, u} r M ⟶ N)
    (h : ∀ (W : (Opens T)ᵒᵖ) (m : M.val.obj W),
      f.val.app W ((tensorUnit r M).app W
        ((1 : C.obj.obj W) ⊗ₜ[D.obj.obj W,(r.hom.app W).hom] m)) =
      g.val.app W ((tensorUnit r M).app W
        ((1 : C.obj.obj W) ⊗ₜ[D.obj.obj W,(r.hom.app W).hom] m))) : f = g := by
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 (𝓡 C).obj)).injective
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  exact h W m

private theorem changeOfRingsHom_unit (t : A ⟶ B)
    (M N : SheafOfModules.{u} (𝓡 A)) (a : M ⟶ N)
    (W : (Opens T)ᵒᵖ) (m : M.val.obj W) :
    (changeOfRingsHom.{u, u, u} t M a).val.app W ((tensorUnit t M).app W
      ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (t.hom.app W).hom] m)) =
      (tensorUnit t N).app W ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (t.hom.app W).hom]
        (a.val.app W m)) := by
  let p : changeOfRingsPresheaf.{u, u, u} t M ⟶ changeOfRingsPresheaf.{u, u, u} t N :=
    { app := fun W ↦ (ModuleCat.extendScalars (t.hom.app W).hom).map (a.val.app W)
      naturality := changeOfRingsHom_naturality.{u, u, u} t M a }
  have hn := (PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).unit.naturality p
  have hv := congrArg (fun f ↦ f.app W) hn
  have hx := ConcreteCategory.congr_hom hv
    ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (t.hom.app W).hom] m)
  change (tensorUnit t N).app W
    ((ModuleCat.extendScalars (t.hom.app W).hom).map (a.val.app W) _) =
      (changeOfRingsHom.{u, u, u} t M a).val.app W ((tensorUnit t M).app W _) at hx
  rw [ModuleCat.ExtendScalars.map_tmul] at hx
  exact hx.symm

private theorem comparison_naturality
    (r : D ⟶ C) (s : D ⟶ A) (b : C ⟶ B) (t : A ⟶ B)
    (h : r ≫ b = s ≫ t) (M N : SheafOfModules.{u} (𝓡 A)) (a : M ⟶ N) :
    changeOfRingsHom.{u, u, u} r ((restrictScalars (𝓻 s)).obj M) ((restrictScalars (𝓻 s)).map a) ≫
      comparison r s b t h N = comparison r s b t h M ≫
        (restrictScalars (𝓻 b)).map (changeOfRingsHom.{u, u, u} t M a) := by
  apply tensorHom_ext
  intro W m
  change (comparison r s b t h N).val.app W
    ((changeOfRingsHom.{u, u, u} r ((restrictScalars (𝓻 s)).obj M)
      ((restrictScalars (𝓻 s)).map a)).val.app W _) =
    (changeOfRingsHom.{u, u, u} t M a).val.app W ((comparison r s b t h M).val.app W _)
  rw [changeOfRingsHom_unit, comparison_tmul, comparison_tmul]
  simp only [map_one]
  rw [changeOfRingsHom_unit]
  rfl

/-- Tensor cancellation across a pushout, naturally in the module, including its tensor unit.
Source: Stacks Project, Tag 01SB (tensor construction and elucidation), Tag 008A.
Proof: sheafify the presheaf of rings W ↦ C(W) tensor over D(W) with A(W).
A pair of maps out of C and A agreeing on D defines on each open the ring map
c tensor a ↦ u(c)v(a); these maps commute with restriction and uniquely extend through
sheafification. Thus this sheaf is a pushout, and its canonical map to B is an isomorphism.
Put L = sheafification of W ↦ C(W) tensor over D(W) with M(W). The formula
(c tensor a)(c' tensor m) = cc' tensor (a • m) defines the pushout-ring action on L:
balancing proves well-definedness before sheafification, local representatives extend it,
and uniqueness of sheaf gluing proves independence and all action laws.
The A-linear map m ↦ sheafification(1 tensor m) then extends B-linearly to
B tensor over A with M, by β tensor m ↦ β • sheafification(1 tensor m).
After restricting to C this is the forward comparison. Its inverse is the sheafification
of c tensor m ↦ b(c) tensor m; D-balancing follows from r followed by b = s followed by t.
The forward-inverse composite fixes c tensor m. For the other composite, locally write
β as a sum of c tensor a in the sheafified pushout. A-balancing gives
b(c)t(a) tensor m = b(c) tensor (a • m), so it fixes β tensor m locally, hence globally.
These formulas commute with every restriction and with each linear map M → N, proving
naturality. The inverse takes 1 tensor m to b(1) tensor m = 1 tensor m on every open.
All constructions use balanced tensor relations and sheaf gluing, with no flatness or
nonzero-ring assumption; the zero module and empty open are included.
(blueprint: lem-weil-pbc-sheaf-tensor-pushout-cancellation). -/
theorem sheafTensorPushoutCancellation
    (r : D ⟶ C) (s : D ⟶ A) (b : C ⟶ B) (t : A ⟶ B)
    (hp : IsPushout r s b t) :
    ∃ e : ∀ M : SheafOfModules.{u} (𝓡 A),
      (restrictScalars (𝓻 b)).obj (changeOfRings.{u, u, u} t M) ≅
        changeOfRings.{u, u, u} r ((restrictScalars (𝓻 s)).obj M),
      (∀ (M N : SheafOfModules.{u} (𝓡 A)) (a : M ⟶ N),
        (restrictScalars (𝓻 b)).map (changeOfRingsHom t M a) ≫ (e N).hom =
          (e M).hom ≫ changeOfRingsHom r ((restrictScalars (𝓻 s)).obj M)
            ((restrictScalars (𝓻 s)).map a)) ∧
      (∀ (M : SheafOfModules.{u} (𝓡 A)) (W : (Opens T)ᵒᵖ) (m : M.val.obj W),
        (e M).inv.val.app W
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 C).obj)).unit.app
            (changeOfRingsPresheaf.{u, u, u} r ((restrictScalars (𝓻 s)).obj M))).app W
            ((1 : C.obj.obj W) ⊗ₜ[D.obj.obj W, (r.hom.app W).hom] m)) =
        ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).unit.app
          (changeOfRingsPresheaf.{u, u, u} t M)).app W 
          ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (t.hom.app W).hom] m)) := by
  let f := comparison r s b t hp.w
  have hu (M : SheafOfModules.{u} (𝓡 A)) (W : (Opens T)ᵒᵖ) (m : M.val.obj W) :
      (f M).val.app W ((tensorUnit r ((restrictScalars (𝓻 s)).obj M)).app W
        ((1 : C.obj.obj W) ⊗ₜ[D.obj.obj W,(r.hom.app W).hom] m)) =
      (tensorUnit t M).app W ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W,(t.hom.app W).hom] m) := by
    dsimp only [f]
    rw [comparison_tmul]
    simp only [map_one]
  have (M : SheafOfModules.{u} (𝓡 A)) : IsIso (f M) :=
    sheafTensorPushoutComparison_isIso r s b t hp M (f M) (hu M)
  refine ⟨fun M ↦ (asIso (f M)).symm, ?_, ?_⟩
  · intro M N a
    change (restrictScalars (𝓻 b)).map (changeOfRingsHom t M a) ≫ inv (f N) =
      inv (f M) ≫ changeOfRingsHom r ((restrictScalars (𝓻 s)).obj M)
        ((restrictScalars (𝓻 s)).map a)
    apply (cancel_mono (f N)).1
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [Category.assoc, comparison_naturality]
    simp
  · intro M W m
    exact hu M W m

end
end SheafOfModules
