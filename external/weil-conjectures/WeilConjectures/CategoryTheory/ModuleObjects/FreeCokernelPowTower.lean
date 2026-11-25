/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.Abelian.CokernelPowTower
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Limits

/-!
# `ℓ`-adic completeness of the regular module

Let `S` be a monoid object in a monoidal preadditive category `C` with cokernels, such that
`S ⊗ -` preserves cokernels. The free `S`-modules `S ⊗ 𝟙/ℓⁿ` on the reductions of the unit
form a tower of `S`-modules, receiving the cone `S ≅ S ⊗ 𝟙 ⟶ S ⊗ 𝟙/ℓⁿ`
(`CategoryTheory.Mod.freeCokernelPowTowerCone`). If `S` is `ℓ`-adically complete and separated
in `C`, this cone is a limit cone of `S`-modules
(`CategoryTheory.Mod.isLimitFreeCokernelPowTowerCone`): the forgetful functor reflects limits,
and its image is the cone of reductions `S ⟶ S/ℓⁿ`, as `S ⊗ -` preserves cokernels.
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

namespace CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
  [MonoidalPreadditive C]

/-- Whiskering commutes with integer multiples of the identity. -/
lemma whiskerLeft_zsmul_id (X Y : C) (k : ℤ) : X ◁ (k • 𝟙 Y) = k • 𝟙 (X ⊗ Y) :=
  ((tensorLeft X).map_zsmul (f := 𝟙 Y) (r := k)).trans (congrArg (k • ·) ((tensorLeft X).map_id Y))

/-- The right unitor intertwines `k : X ⟶ X` and `X ◁ k : X ⊗ 𝟙 ⟶ X ⊗ 𝟙`. -/
lemma zsmul_id_comp_rightUnitor_inv (X : C) (k : ℤ) :
    (k • 𝟙 X) ≫ (ρ_ X).inv = (ρ_ X).inv ≫ X ◁ (k • 𝟙 (𝟙_ C)) := by
  rw [whiskerLeft_zsmul_id, Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.id_comp,
    Category.comp_id]

end CategoryTheory.MonoidalCategory

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (S : C) [MonObj S]

/-- The regular module `S` is the free module `S ⊗ 𝟙` on the unit, via the right unitor. -/
def regularIsoFreeFunctorObjUnit : regular S ≅ (freeFunctor S).obj (𝟙_ C) :=
  isoMk (M := regular S) (N := (freeFunctor S).obj (𝟙_ C)) (ρ_ S).symm (by
    have h : μ[S] ≫ (ρ_ S).inv = S ◁ (ρ_ S).inv ≫ (α_ S S (𝟙_ C)).inv ≫ μ[S] ▷ 𝟙_ C := by
      rw [rightUnitor_inv_naturality, rightUnitor_tensor_inv, Category.assoc]
    exact h)

@[simp]
lemma regularIsoFreeFunctorObjUnit_hom_hom :
    (regularIsoFreeFunctorObjUnit S).hom.hom = (ρ_ S).inv :=
  rfl

variable [Preadditive C] [HasCokernels C]

/-- The cone of `S`-modules `S ≅ S ⊗ 𝟙 ⟶ S ⊗ 𝟙/ℓⁿ` over the free modules on the reductions of
the unit modulo the powers of `ℓ`. -/
noncomputable def freeCokernelPowTowerCone (ℓ : ℕ) :
    Cone (cokernelPowTower (𝟙_ C) ℓ ⋙ Mod.freeFunctor S) :=
  ((freeFunctor S).mapCone (cokernelPowTowerCone (𝟙_ C) ℓ)).extend
    (regularIsoFreeFunctorObjUnit S).hom

@[simp]
lemma freeCokernelPowTowerCone_pt (ℓ : ℕ) : (freeCokernelPowTowerCone S ℓ).pt = regular S :=
  rfl

@[simp]
lemma freeCokernelPowTowerCone_π_app_hom (ℓ n : ℕ) :
    ((freeCokernelPowTowerCone S ℓ).π.app (op n)).hom =
      (ρ_ S).inv ≫ S ◁ cokernel.π (((ℓ ^ n : ℕ) : ℤ) • 𝟙 (𝟙_ C)) :=
  rfl

variable [MonoidalPreadditive C] [PreservesColimitsOfShape WalkingParallelPair (tensorLeft S)]

/-- The `n`-th leg `S ≅ S ⊗ 𝟙 ⟶ S ⊗ 𝟙/ℓⁿ` of `freeCokernelPowTowerCone S ℓ` is, in `C`, a
cokernel of `ℓⁿ`, as `S ⊗ -` preserves cokernels. -/
noncomputable def isColimitCokernelCoforkFreeCokernelPowTowerCone (ℓ n : ℕ) :
    IsColimit (CokernelCofork.ofπ (f := ((ℓ ^ n : ℕ) : ℤ) • 𝟙 S)
      ((ρ_ S).inv ≫ S ◁ cokernel.π (((ℓ ^ n : ℕ) : ℤ) • 𝟙 (𝟙_ C))) (by
        rw [← Category.assoc, zsmul_id_comp_rightUnitor_inv, Category.assoc,
          ← MonoidalCategory.whiskerLeft_comp, cokernel.condition,
          MonoidalPreadditive.whiskerLeft_zero, Limits.comp_zero])) :=
  isColimitCokernelCoforkOfIsoHomComp (ρ_ S).symm (zsmul_id_comp_rightUnitor_inv S _) (by
      rw [← MonoidalCategory.whiskerLeft_comp, cokernel.condition,
        MonoidalPreadditive.whiskerLeft_zero])
    (isColimitCoforkMapOfIsColimit' (tensorLeft S) (cokernel.condition _) (cokernelIsCokernel _))

/-- **The regular module is `ℓ`-adically complete**: if `S` is `ℓ`-adically complete and
separated in `C` and `S ⊗ -` preserves cokernels, then the regular module `S` is the limit of
the free `S`-modules `S ⊗ 𝟙/ℓⁿ`. -/
noncomputable def isLimitFreeCokernelPowTowerCone (ℓ : ℕ)
    (h : IsLimit (cokernelPowTowerCone S ℓ)) : IsLimit (freeCokernelPowTowerCone S ℓ) :=
  isLimitOfReflects (forget S) (isLimitOfIsColimitCokernelCofork _ _
    (isColimitCokernelCoforkFreeCokernelPowTowerCone S ℓ) h)

end CategoryTheory.Mod
