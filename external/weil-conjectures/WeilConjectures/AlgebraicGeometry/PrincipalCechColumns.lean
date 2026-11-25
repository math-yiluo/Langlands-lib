/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechTotal
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Explicit principal Čech columns and horizontal maps

Source: Stacks, Tag 08D1, alternating Čech double complex
(blueprint: def-sc-principal-cech-columns).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry
noncomputable section

variable {A : Type u} [CommRing A] (r : ℕ) (f : Fin r → A)

/-- Nonempty subsets in horizontal degree p. Source: Stacks, Tag 08D1
(blueprint: def-sc-principal-cech-columns). -/
def principalCechRowIndex (p : ℤ) :=
  {S : {S : Finset (Fin r) // S.Nonempty} // (S.val.card : ℤ) = p + 1}

/-- Section complexes at a subset. Source: Stacks, Tag 08D1
(blueprint: def-sc-principal-cech-columns). -/
def principalCechSectionFunctor (S : Finset (Fin r)) :=
  (affineOpenSections A (principalCechIntersection r f S)).mapHomologicalComplex
    (ComplexShape.up ℤ)

/-- The product column functor. Source: Stacks, Tag 08D1
(blueprint: def-sc-principal-cech-columns). -/
def principalCechColumnFunctor (p : ℤ) :
    CochainComplex (SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace)) ℤ ⥤ CochainComplex (ModuleCat.{u} A) ℤ where
  obj F := ∏ᶜ fun S : principalCechRowIndex r p ↦
    (principalCechSectionFunctor r f S.val.val).obj F
  map i := Limits.Pi.map fun S ↦ (principalCechSectionFunctor r f S.val.val).map i
  map_id F := by simp
  map_comp i j := by simp [← Limits.Pi.map_comp_map]

/-- Restriction from the erased intersection to the original one.
Source: Stacks, Tag 08D1 (blueprint: def-sc-principal-cech-columns). -/
def principalCechEraseRestriction (S : Finset (Fin r)) (j : Fin r) :
    principalCechSectionFunctor r f (S.erase j) ⟶ principalCechSectionFunctor r f S :=
  NatTrans.mapHomologicalComplex
    (show affineOpenSections A (principalCechIntersection r f (S.erase j)) ⟶
        affineOpenSections A (principalCechIntersection r f S) from
      { app F := (modulesSpecToSheaf.obj F).obj.map
          (homOfLE (principalCechIntersection_erase_le r f S j)).op
        naturality := by
          intro F G i
          exact ((modulesSpecToSheaf.map i).hom.naturality _).symm })
    (ComplexShape.up ℤ)

/-- Deletion lowers the horizontal degree by one. Source: Stacks, Tag 08D1
(blueprint: def-sc-principal-cech-columns).
Proof: erasing a member lowers cardinality by one; use the row's cardinality equation. -/
theorem principalCechRowIndex_erase_card (p : ℤ)
    (S : principalCechRowIndex r (p + 1)) (j : S.val.val) :
    ((S.val.val.erase j.val).card : ℤ) = p + 1 := by
  have h := Finset.card_erase_add_one j.property
  have hc := S.property
  have he : ((S.val.val.erase j.val).card : ℤ) + 1 = S.val.val.card := by
    exact_mod_cast h
  omega

/-- The alternating horizontal differential, with empty deletions omitted.
Source: Stacks, Tag 08D1 (blueprint: def-sc-principal-cech-columns). -/
def principalCechHorizontal (p : ℤ) :
    principalCechColumnFunctor r f p ⟶ principalCechColumnFunctor r f (p + 1) where
  app F := Limits.Pi.lift fun S ↦ ∑ j : S.val.val,
    if h : (S.val.val.erase j.val).Nonempty then
      ((-1 : ℤ) ^ (S.val.val.filter (fun k ↦ k < j.val)).card) •
        (Limits.Pi.π (fun T : principalCechRowIndex r p ↦
          (principalCechSectionFunctor r f T.val.val).obj F)
          ⟨⟨S.val.val.erase j.val, h⟩, principalCechRowIndex_erase_card r p S j⟩ ≫
          (principalCechEraseRestriction r f S.val.val j.val).app F)
    else 0
  naturality := by
    intro F G i
    apply Limits.Pi.hom_ext
    intro S
    simp only [principalCechColumnFunctor, Category.assoc, Limits.Pi.map_π,
      Limits.Pi.lift_comp_π_assoc, Limits.Pi.lift_comp_π, Preadditive.comp_sum,
      Preadditive.sum_comp]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs with h
    · simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp,
        Limits.Pi.map_π_assoc, Category.assoc]
      rw [← NatTrans.naturality]
    · simp

/-- A column outside the finite range is zero. Source: Stacks, Tag 08D1
(blueprint: def-sc-principal-cech-columns).
Proof: a nonempty subset has cardinality between one and r, so the indexing type
is empty outside the range. The empty categorical product is zero in an additive category. -/
theorem principalCechColumn_isZero (p : ℤ) (hp : p < 0 ∨ (r : ℤ) - 1 < p)
    (F : CochainComplex (SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) :
    IsZero ((principalCechColumnFunctor r f p).obj F) := by
  have hnone (S : principalCechRowIndex r p) : False := by
    have hpos := Finset.card_pos.mpr S.val.property
    have hle := Finset.card_le_univ S.val.val
    simp only [Fintype.card_fin] at hle
    have hc := S.property
    rcases hp with hp | hp <;> omega
  apply (IsZero.iff_id_eq_zero _).mpr
  apply Limits.Pi.hom_ext
  intro S
  exact (hnone S).elim

/-- Finite products of section quasi-isomorphisms give a column quasi-isomorphism.
Source: Stacks, Tag 08D1 (blueprint: def-sc-principal-cech-columns).
Proof: the additive homology functor preserves finite products. The product comparison
identifies the homology map with a product of isomorphisms. No horizontal differential
or coefficient boundedness is used. -/
theorem principalCechColumn_quasiIso (p : ℤ)
    (F G : CochainComplex (SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) (i : F ⟶ G)
    (hi : ∀ S : {S : Finset (Fin r) // S.Nonempty},
      QuasiIso ((principalCechSectionFunctor r f S.val).map i)) :
    QuasiIso ((principalCechColumnFunctor r f p).map i) := by
  classical
  have : Finite (principalCechRowIndex r p) := by
    unfold principalCechRowIndex
    infer_instance
  let : Fintype (principalCechRowIndex r p) := Fintype.ofFinite _
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ) n
  let X := fun S : principalCechRowIndex r p ↦
    (principalCechSectionFunctor r f S.val.val).obj F
  let Y := fun S : principalCechRowIndex r p ↦
    (principalCechSectionFunctor r f S.val.val).obj G
  let t := fun S : principalCechRowIndex r p ↦
    (principalCechSectionFunctor r f S.val.val).map i
  have (S : principalCechRowIndex r p) : QuasiIso (t S) := hi S.val
  have (S : principalCechRowIndex r p) : IsIso (H.map (t S)) := by
    exact (quasiIsoAt_iff_isIso_homologyMap (t S) n).mp inferInstance
  have he : H.map (Limits.Pi.map t) ≫ piComparison H Y =
      piComparison H X ≫ Limits.Pi.map (fun S ↦ H.map (t S)) := by
    apply Limits.Pi.hom_ext
    intro S
    dsimp [X, Y, t]
    simp only [Category.assoc, piComparison_comp_π, Limits.Pi.map_π, piComparison_comp_π_assoc]
    rw [← H.map_comp, Limits.Pi.map_π, H.map_comp]
  change IsIso (H.map (Limits.Pi.map t))
  have : IsIso (H.map (Limits.Pi.map t) ≫ piComparison H Y) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (piComparison H Y)

end
end AlgebraicGeometry
