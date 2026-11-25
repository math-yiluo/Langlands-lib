/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.MonoidalCompat
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Exterior powers of presheaves of modules

Let `R` be a presheaf of commutative rings on a category `C` and `M` a presheaf of
`R`-modules. For `r : ℕ`, the exterior power `⋀ʳ M` is the presheaf of modules
`X ↦ ⋀[R(X)]^r M(X)`; the restriction map along `f : X ⟶ Y` is the map
`⋀ʳ M(X) → ⋀ʳ M(Y)`, `m₁ ∧ ⋯ ∧ m_r ↦ f^* m₁ ∧ ⋯ ∧ f^* m_r`, which is semilinear along
`R(X) → R(Y)`.

## Main declarations

- `PresheafOfModules.exteriorPower M r`: the exterior power `⋀ʳ M`.
- `PresheafOfModules.exteriorPower_map_ιMulti`: the restriction maps of `⋀ʳ M` on wedge
  products.
-/

@[expose] public section

universe u

open CategoryTheory

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

local instance instCommRingCarrierObj_exteriorPower
    (X : Cᵒᵖ) : CommRing ((R ⋙ forget₂ CommRingCat RingCat).obj X) :=
  inferInstanceAs (CommRing (R.obj X))

namespace PresheafOfModules

variable (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) (r : ℕ)

namespace ExteriorPower

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `PresheafOfModules.exteriorPower`: the alternating map
`(m₁, …, m_r) ↦ f^* m₁ ∧ ⋯ ∧ f^* m_r`, linear along `R(X) → R(Y)`. -/
noncomputable def mapAlternating {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    M.obj X [⋀^Fin r]→ₗ[(R ⋙ forget₂ CommRingCat RingCat).obj X]
      (ModuleCat.restrictScalars ((R ⋙ forget₂ CommRingCat RingCat).map f).hom).obj
        (ModuleCat.of ((R ⋙ forget₂ CommRingCat RingCat).obj Y)
          (⋀[(R ⋙ forget₂ CommRingCat RingCat).obj Y]^r (M.obj Y))) where
  toFun v := exteriorPower.ιMulti ((R ⋙ forget₂ CommRingCat RingCat).obj Y) r
    fun i ↦ M.restrictₛₗ f (v i)
  map_update_add' v i x y := by
    classical
    have h (z : M.obj X) : (fun j ↦ M.restrictₛₗ f (Function.update v i z j)) =
        Function.update (fun j ↦ M.restrictₛₗ f (v j)) i (M.restrictₛₗ f z) := by
      ext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [hj]
    simp only [h, map_add]
    exact AlternatingMap.map_update_add _ _ _ _ _
  map_update_smul' v i c x := by
    classical
    have h (z : M.obj X) : (fun j ↦ M.restrictₛₗ f (Function.update v i z j)) =
        Function.update (fun j ↦ M.restrictₛₗ f (v j)) i (M.restrictₛₗ f z) := by
      ext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [hj]
    simp only [h, LinearMap.map_smulₛₗ]
    exact AlternatingMap.map_update_smul _ _ _ _ _
  map_eq_zero_of_eq' v i j hv hij :=
    AlternatingMap.map_eq_zero_of_eq _ _ (i := i) (j := j) (by simp only [hv]) hij

/-- Auxiliary definition for `PresheafOfModules.exteriorPower`: the restriction maps. -/
noncomputable def map {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ModuleCat.of ((R ⋙ forget₂ CommRingCat RingCat).obj X)
        (⋀[(R ⋙ forget₂ CommRingCat RingCat).obj X]^r (M.obj X)) ⟶
      (ModuleCat.restrictScalars ((R ⋙ forget₂ CommRingCat RingCat).map f).hom).obj
        (ModuleCat.of ((R ⋙ forget₂ CommRingCat RingCat).obj Y)
          (⋀[(R ⋙ forget₂ CommRingCat RingCat).obj Y]^r (M.obj Y))) :=
  ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars ((R ⋙ forget₂ CommRingCat RingCat).map f).hom).obj
        (ModuleCat.of ((R ⋙ forget₂ CommRingCat RingCat).obj Y)
          (⋀[(R ⋙ forget₂ CommRingCat RingCat).obj Y]^r (M.obj Y))))
    (exteriorPower.alternatingMapLinearEquiv (mapAlternating M r f))

lemma map_ιMulti {X Y : Cᵒᵖ} (f : X ⟶ Y) (v : Fin r → M.obj X) :
    map M r f (exteriorPower.ιMulti _ r v) =
      exteriorPower.ιMulti ((R ⋙ forget₂ CommRingCat RingCat).obj Y) r
        fun i ↦ M.restrictₛₗ f (v i) :=
  (exteriorPower.alternatingMapLinearEquiv_apply_ιMulti (mapAlternating M r f) v :)

lemma map_comp_ιMulti {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (v : Fin r → M.obj X) :
    map M r (f ≫ g) (exteriorPower.ιMulti _ r v) =
      map M r g (map M r f (exteriorPower.ιMulti _ r v)) := by
  rw [map_ιMulti, map_ιMulti, map_ιMulti]
  congr 1
  funext i
  exact M.map_comp_apply f g (v i)

lemma map_id_ιMulti (X : Cᵒᵖ) (v : Fin r → M.obj X) :
    map M r (𝟙 X) (exteriorPower.ιMulti _ r v) = exteriorPower.ιMulti _ r v := by
  rw [map_ιMulti]
  congr 1
  funext i
  rw [restrictₛₗ_apply, PresheafOfModules.map_id]
  rfl

end ExteriorPower

open ExteriorPower in
/-- **The exterior power `⋀ʳ M` of a presheaf of modules**: the presheaf of modules
`X ↦ ⋀[R(X)]^r M(X)`, whose restriction maps send `m₁ ∧ ⋯ ∧ m_r` to `f^* m₁ ∧ ⋯ ∧ f^* m_r`
(`PresheafOfModules.exteriorPower_map_ιMulti`). -/
noncomputable def exteriorPower : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat) where
  obj X := ModuleCat.of _ (⋀[(R ⋙ forget₂ CommRingCat RingCat).obj X]^r (M.obj X))
  map f := ExteriorPower.map M r f
  map_id X := by
    ext v
    exact map_id_ιMulti M r X v
  map_comp f g := by
    ext v
    exact map_comp_ιMulti M r f g v

/-- The restriction maps of the exterior power on wedge products:
`f^* (m₁ ∧ ⋯ ∧ m_r) = f^* m₁ ∧ ⋯ ∧ f^* m_r`. -/
lemma exteriorPower_map_ιMulti {X Y : Cᵒᵖ} (f : X ⟶ Y) (v : Fin r → M.obj X) :
    (M.exteriorPower r).map f (exteriorPower.ιMulti _ r v) =
      exteriorPower.ιMulti ((R ⋙ forget₂ CommRingCat RingCat).obj Y) r
        fun i ↦ M.restrictₛₗ f (v i) :=
  ExteriorPower.map_ιMulti M r f v

end PresheafOfModules
