/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralOperationsWellDefined

/-!
# Towers occurring in the Milnor sequence

The existing generic tower constructions of `ProEtaleMilnorSequence` live here so
that the cone calculation and its degree-zero specialization share their definitions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe a b

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

section Cokernel

variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]

/-- The sheaf cokernel of 1-T on a tower product, using the existing transition map.
(blueprint: proposition-milnor-sequence--2). -/
abbrev milnorTowerCokernel (M : ℕᵒᵖ ⥤ A) : A :=
  cokernel (towerTransitionEndomorphism (K := fun n : ℕ ↦ M.obj (op n))
    (fun n : ℕ ↦ M.map (homOfLE (Nat.le_succ n)).op))

/-- The canonical map of these cokernels induced by a tower morphism.
(blueprint: proposition-milnor-sequence--2). -/
def milnorTowerCokernelMap {M N : ℕᵒᵖ ⥤ A} (f : M ⟶ N) :
    milnorTowerCokernel M ⟶ milnorTowerCokernel N :=
  cokernel.map
    (towerTransitionEndomorphism (K := fun n : ℕ ↦ M.obj (op n))
      (fun n ↦ M.map (homOfLE (Nat.le_succ n)).op))
    (towerTransitionEndomorphism (K := fun n : ℕ ↦ N.obj (op n))
      (fun n ↦ N.map (homOfLE (Nat.le_succ n)).op))
    (Limits.Pi.map (fun n : ℕ ↦ f.app (op n)))
    (Limits.Pi.map (fun n : ℕ ↦ f.app (op n)))
    (towerTransitionEndomorphism_natural_backward _ _ _
      (fun n ↦ (f.naturality (homOfLE (Nat.le_succ n)).op).symm)).symm

/-- The tower of q-th cohomology sheaves, with induced transition maps.
(blueprint: proposition-milnor-sequence--2). -/
abbrev milnorCohomologyTower (K : ℕᵒᵖ ⥤ CochainComplex A ℤ) (q : ℤ) : ℕᵒᵖ ⥤ A :=
  K ⋙ HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q

/-- Regard a module tower as complexes concentrated in degree zero.
(blueprint: proposition-milnor-sequence--2). -/
abbrev milnorSingleTower (M : ℕᵒᵖ ⥤ A) : ℕᵒᵖ ⥤ CochainComplex A ℤ :=
  M ⋙ HomologicalComplex.single A (ComplexShape.up ℤ) 0

end Cokernel

end AlgebraicGeometry.Scheme.ProEt
