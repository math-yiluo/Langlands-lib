/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Balanced contraction on sheaf tensors

Source: Stacks Project, Cohomology, Tag 08DE, proof.
(blueprint: lem-pc-balanced-sheaf-tensor-contraction)
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory MonoidalCategory TopologicalSpace
open scoped ChangeOfRings

namespace SheafOfModules

variable {Z : TopCat.{u}} {R B : Z.Sheaf CommRingCat.{u}}

set_option hygiene false in
local notation "𝓡" E =>
  (sheafCompose (Opens.grothendieckTopology Z) (forget₂ CommRingCat.{u} RingCat.{u})).obj E
set_option hygiene false in
local notation "𝓻" a =>
  (sheafCompose (Opens.grothendieckTopology Z) (forget₂ CommRingCat.{u} RingCat.{u})).map a

section CoefficientComparison

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  {R₀ B₀ : Sheaf J RingCat.{u}}

private noncomputable def restrictSheafificationComparison
    (α : R₀ ⟶ B₀) (P : PresheafOfModules.{u} B₀.obj) :
    (PresheafOfModules.sheafification (𝟙 R₀.obj)).obj
      ((PresheafOfModules.restrictScalars α.hom).obj P) ⟶
        (restrictScalars α).obj
          ((PresheafOfModules.sheafification (𝟙 B₀.obj)).obj P) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 R₀.obj)).symm
    ((PresheafOfModules.restrictScalars α.hom).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 B₀.obj)).unit.app P))

private theorem restrictSheafificationComparison_isIso
    (α : R₀ ⟶ B₀) (P : PresheafOfModules.{u} B₀.obj) :
    IsIso (restrictSheafificationComparison α P) := by
  rw [← isIso_iff_of_reflects_iso _ (toSheaf R₀)]
  have he : (toSheaf R₀).map (restrictSheafificationComparison α P) = 𝟙 _ := by
    unfold restrictSheafificationComparison
    rw [PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
    apply ((CategoryTheory.sheafificationAdjunction
      J AddCommGrpCat.{u}).homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    rfl
  rw [he]
  infer_instance

private theorem restrictSheafificationComparison_unit
    (α : R₀ ⟶ B₀) (P : PresheafOfModules.{u} B₀.obj)
    (W : Cᵒᵖ) (x : P.obj W) :
    (restrictSheafificationComparison α P).val.app W
        (((PresheafOfModules.sheafificationAdjunction (𝟙 R₀.obj)).unit.app
          ((PresheafOfModules.restrictScalars α.hom).obj P)).app W x) =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 B₀.obj)).unit.app P).app W x := by
  have h := (PresheafOfModules.sheafificationHomEquiv
    (P := (PresheafOfModules.restrictScalars α.hom).obj P)
    (F := (restrictScalars α).obj
      ((PresheafOfModules.sheafification (𝟙 B₀.obj)).obj P))
    (𝟙 R₀.obj)).apply_symm_apply
    ((PresheafOfModules.restrictScalars α.hom).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 B₀.obj)).unit.app P))
  exact congrArg (fun k ↦ (k.app W) x) h

end CoefficientComparison

private noncomputable def contractionApp
    (α : R ⟶ B) (M : SheafOfModules.{u} (𝓡 B))
    (N : SheafOfModules.{u} (𝓡 R)) (W : (Opens Z)ᵒᵖ) :
    ((PresheafOfModules.restrictScalars (𝓻 α).hom).obj
      (M.val ⊗ changeOfRingsPresheaf.{u, u, u} α N)).obj W ⟶
        (((restrictScalars (𝓻 α)).obj M).val ⊗ N.val).obj W := by
  let A := R.obj.obj W
  let C := B.obj.obj W
  let ρ := (α.hom.app W).hom
  let : Algebra A C := ρ.toAlgebra
  let : Module A (M.val.obj W) := Module.compHom (M.val.obj W) ρ
  let : IsScalarTower A C (M.val.obj W) :=
    IsScalarTower.of_algebraMap_smul (fun r m ↦ rfl)
  exact (TensorProduct.AlgebraTensorModule.cancelBaseChange A C C
    (M.val.obj W) (N.val.obj W)).restrictScalars A |>.toModuleIso.hom

private theorem contractionApp_tmul
    (α : R ⟶ B) (M : SheafOfModules.{u} (𝓡 B))
    (N : SheafOfModules.{u} (𝓡 R)) (W : (Opens Z)ᵒᵖ)
    (m : M.val.obj W) (b : B.obj.obj W) (n : N.val.obj W) :
    contractionApp α M N W
        (m ⊗ₜ[B.obj.obj W] (b ⊗ₜ[R.obj.obj W,(α.hom.app W).hom] n)) =
      (show ((restrictScalars (𝓻 α)).obj M).val.obj W from b • m)
        ⊗ₜ[R.obj.obj W] n := by
  rfl

-- Tensor restrictions with two coefficient rings need extra definitional equality checks.
private noncomputable def contractionPresheaf
    (α : R ⟶ B) (M : SheafOfModules.{u} (𝓡 B))
    (N : SheafOfModules.{u} (𝓡 R)) :
    (PresheafOfModules.restrictScalars (𝓻 α).hom).obj
      (M.val ⊗ changeOfRingsPresheaf.{u, u, u} α N) ⟶
        ((restrictScalars (𝓻 α)).obj M).val ⊗ N.val where
  app W := contractionApp α M N W
  naturality {U V} i := by
    ext t
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul m z =>
      induction z using TensorProduct.inductionOn with
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
      | tmul b n =>
        change contractionApp α M N V
            (show (M.val ⊗ changeOfRingsPresheaf.{u, u, u} α N).obj V from
              (M.val ⊗ changeOfRingsPresheaf.{u, u, u} α N).map i
                (m ⊗ₜ[B.obj.obj U] (b ⊗ₜ[R.obj.obj U,(α.hom.app U).hom] n))) =
          ((((restrictScalars (𝓻 α)).obj M).val ⊗ N.val).map i)
            (contractionApp α M N U
              (m ⊗ₜ[B.obj.obj U] (b ⊗ₜ[R.obj.obj U,(α.hom.app U).hom] n)))
        erw [PresheafOfModules.Monoidal.tensorObj_map_tmul]
        erw [Classical.choose_spec (exists_changeOfRingsMap.{u, u, u} α N i)]
        refine (contractionApp_tmul α M N V (M.val.map i m) (B.obj.map i b)
          (N.val.map i n)).trans ?_
        erw [contractionApp_tmul α M N U m b n]
        erw [PresheafOfModules.Monoidal.tensorObj_map_tmul]
        exact congrArg (fun x : M.val.obj V ↦
          (show ((restrictScalars (𝓻 α)).obj M).val.obj V from x)
            ⊗ₜ[R.obj.obj V] (show N.val.obj V from N.val.map i n)) (M.val.map_smul i b m).symm

-- The coefficient comparison and tensor sheafification require extra equality checks.
/-- The sectionwise balanced contraction descends to the sheaf tensor.
Source: Stacks Project, Cohomology, Tag 08DE, proof; Modules on Sites, Tag 0GMW.

Proof: construct the sectionwise R-linear contraction by restricting Mathlib's
cancelBaseChange equivalence. Its formula is `m ⊗ (b ⊗ n) ↦ (b • m) ⊗ n`.
Two tensor inductions show compatibility with restrictions, since both factors restrict
and M's restriction carries b • m to the restricted scalar acting on the restricted m.
The canonical comparison from R-sheafification of a restricted B-presheaf to restriction
of its B-sheafification extends the restricted B-unit. Forget to abelian sheaves: this
comparison is the identity of the same abelian sheafification. Thus it is invertible.
The extension presheaf unit is inverted by B-sheafification. W_whiskerLeft preserves
this property after tensoring with M.val. Sheafify that tensor map and compose with
tensorObjIsoSheafification.inv to obtain an isomorphism onto M tensor_B E. Restrict
this isomorphism, invert it and the preceding coefficient comparison, and compose with
R-sheafification of the presheaf contraction and tensorObjIsoSheafification.inv.
Naturality of both units gives the claimed section formula. No inverse identity for
the forward map is asserted here. Zero rings, zero modules and empty spaces are included.
(blueprint: lem-pc-balanced-sheaf-tensor-contraction) -/
theorem exists_balancedTensorContraction (α : R ⟶ B)
    (M : SheafOfModules.{u} (𝓡 B)) (N : SheafOfModules.{u} (𝓡 R)) :
    ∃ ψ : (restrictScalars (𝓻 α)).obj
        ((monoidalCategory B).tensorObj M (changeOfRings.{u, u, u} α N)) ⟶
      (monoidalCategory R).tensorObj ((restrictScalars (𝓻 α)).obj M) N,
      ∀ (W : (Opens Z)ᵒᵖ) (m : M.val.obj W) (b : B.obj.obj W) (n : N.val.obj W),
      ψ.val.app W
        ((tensorObjIsoSheafification M (changeOfRings.{u, u, u} α N)).inv.val.app W
        (((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).unit.app
          (M.val ⊗ (changeOfRings.{u, u, u} α N).val)).app W
            (m ⊗ₜ[B.obj.obj W]
              ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).unit.app
                (changeOfRingsPresheaf.{u, u, u} α N)).app W
                  (b ⊗ₜ[R.obj.obj W,(α.hom.app W).hom] n)))) =
      (tensorObjIsoSheafification ((restrictScalars (𝓻 α)).obj M) N).inv.val.app W
        (((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 R).obj)).unit.app
          (((restrictScalars (𝓻 α)).obj M).val ⊗ N.val)).app W
            ((b • m) ⊗ₜ[R.obj.obj W] n)) := by
  let := monoidalCategory B
  let E := changeOfRingsPresheaf.{u, u, u} α N
  let SB := PresheafOfModules.sheafification (𝟙 (𝓡 B).obj)
  let SR := PresheafOfModules.sheafification (𝟙 (𝓡 R).obj)
  let adjB := PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)
  let η := adjB.unit.app E
  have hη : (Opens.grothendieckTopology Z).W
      ((PresheafOfModules.toPresheaf (𝓡 B).obj).map η) := by
    change ((Opens.grothendieckTopology Z).W.inverseImage
      (PresheafOfModules.toPresheaf (𝓡 B).obj)) η
    rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (𝟙 (𝓡 B).obj)]
    change IsIso (SB.map η)
    infer_instance
  have hl := W_whiskerLeft B M.val hη
  have : IsIso (SB.map (M.val ◁ η)) := by
    rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (𝟙 (𝓡 B).obj)] at hl
    exact hl
  let i := asIso (SB.map (M.val ◁ η)) ≪≫
    (tensorObjIsoSheafification M (SB.obj E)).symm
  let q := (restrictScalars (𝓻 α)).mapIso i
  have : IsIso (restrictSheafificationComparison (𝓻 α) (M.val ⊗ E)) :=
    restrictSheafificationComparison_isIso (𝓻 α) (M.val ⊗ E)
  let j := asIso (restrictSheafificationComparison (𝓻 α) (M.val ⊗ E))
  let c := SR.map (contractionPresheaf α M N) ≫
    (tensorObjIsoSheafification ((restrictScalars (𝓻 α)).obj M) N).inv
  refine ⟨q.inv ≫ j.inv ≫ c, ?_⟩
  intro W m b n
  let t := m ⊗ₜ[B.obj.obj W] (b ⊗ₜ[R.obj.obj W,(α.hom.app W).hom] n)
  let uB := (adjB.unit.app (M.val ⊗ E)).app W t
  let uR := ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 R).obj)).unit.app
    ((PresheafOfModules.restrictScalars (𝓻 α).hom).obj (M.val ⊗ E))).app W t
  have hj : j.hom.val.app W uR = uB :=
    restrictSheafificationComparison_unit (𝓻 α) (M.val ⊗ E) W t
  have hq := adjB.unit.naturality (M.val ◁ η)
  have hq' := congrArg (fun k ↦ (k.app W) t) hq
  change (adjB.unit.app (M.val ⊗ (SB.obj E).val)).app W
      (m ⊗ₜ[B.obj.obj W] η.app W (b ⊗ₜ[R.obj.obj W,(α.hom.app W).hom] n)) =
    (SB.map (M.val ◁ η)).val.app W uB at hq'
  let pB := (tensorObjIsoSheafification M (SB.obj E)).inv.val.app W
    ((adjB.unit.app (M.val ⊗ (SB.obj E).val)).app W
      (m ⊗ₜ[B.obj.obj W] η.app W (b ⊗ₜ[R.obj.obj W,(α.hom.app W).hom] n)))
  have hp : q.hom.val.app W uB = pB := by
    change (tensorObjIsoSheafification M (SB.obj E)).inv.val.app W
      ((SB.map (M.val ◁ η)).val.app W uB) = _
    rw [← hq']
  have hiq : q.inv.val.app W pB = uB := by
    rw [← hp]
    exact congrArg (fun k ↦ k.val.app W uB) q.hom_inv_id
  have hij : j.inv.val.app W uB = uR := by
    rw [← hj]
    exact congrArg (fun k ↦ k.val.app W uR) j.hom_inv_id
  have hn := (PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 R).obj)).unit.naturality
    (contractionPresheaf α M N)
  have he := congrArg (fun k ↦ (k.app W) t) hn
  change ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 R).obj)).unit.app
      (((restrictScalars (𝓻 α)).obj M).val ⊗ N.val)).app W
        (contractionApp α M N W t) =
    (SR.map (contractionPresheaf α M N)).val.app W uR at he
  change c.val.app W (j.inv.val.app W (q.inv.val.app W pB)) = _
  -- Compose section equalities without rewriting through the comparison maps.
  refine (congrArg (c.val.app W)
    ((congrArg (j.inv.val.app W) hiq).trans hij)).trans ?_
  change (tensorObjIsoSheafification ((restrictScalars (𝓻 α)).obj M) N).inv.val.app W
    ((SR.map (contractionPresheaf α M N)).val.app W uR) = _
  exact congrArg
    ((tensorObjIsoSheafification ((restrictScalars (𝓻 α)).obj M) N).inv.val.app W)
    (he.symm.trans (congrArg
      (((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 R).obj)).unit.app
        (((restrictScalars (𝓻 α)).obj M).val ⊗ N.val)).app W)
      (contractionApp_tmul α M N W m b n)))

end SheafOfModules
