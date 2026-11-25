/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Functor.OfSequence

import Mathlib.Algebra.Category.ModuleCat.Products
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts

/-!
# Surjective towers of module complexes

Source: Stacks Project, Tags 091D (3), (5) and 0CQD
(blueprint: lem-weil-pbc-surjective-module-complex-tower-limit).
Natural index `n` denotes the source's positive index `n + 1`.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

private theorem module_countableAB4Star (R : Type u) [Ring R] :
    CountableAB4Star (ModuleCat.{v} R) := by
  let U := forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}
  have : PreservesFiniteColimits U := ⟨fun J _ _ ↦
    ModuleCat.forget₂PreservesColimitsOfShape.{v, u, 0, 0} R J⟩
  have : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{v} R) :=
    HasExactLimitsOfShape.domain_of_functor (Discrete ℕ)
      (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v})
  have : HasFiniteBiproducts (ModuleCat.{v} R) := Abelian.hasFiniteBiproducts
  exact CountableAB4Star.of_hasExactLimitsOfShape_nat _

private theorem epi_one_sub
    {R : Type u} [Ring R] {F : ℕᵒᵖ ⥤ ModuleCat.{v} R}
    {B : Fan (fun n : ℕ ↦ F.obj (Opposite.op n))} (hB : IsLimit B)
    (s : B.pt ⟶ B.pt)
    (hs : ∀ n : ℕ, s ≫ B.proj n =
      B.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op)
    (hF : ∀ n : ℕ, Epi (F.map (homOfLE n.le_succ).op)) :
    Epi (𝟙 B.pt - s) := by
  classical
  let M := fun n : ℕ ↦ F.obj (Opposite.op n)
  let e : B.pt ≅ ModuleCat.of R (∀ n, M n) :=
    hB.conePointUniqueUpToIso (ModuleCat.productConeIsLimit M)
  have he (n : ℕ) (x : B.pt) : e.hom x n = B.proj n x := by
    exact ConcreteCategory.congr_hom
      (hB.conePointUniqueUpToIso_hom_comp (ModuleCat.productConeIsLimit M) ⟨n⟩) x
  rw [ModuleCat.epi_iff_surjective]
  intro y
  have hsurj (n : ℕ) := (ModuleCat.epi_iff_surjective _).mp (hF n)
  let x : ∀ n : ℕ, M n := fun n ↦ Nat.rec (motive := fun n ↦ M n) 0
    (fun n xn ↦ (hsurj n (xn - B.proj n y)).choose) n
  have hx (n : ℕ) : F.map (homOfLE n.le_succ).op (x (n + 1)) =
      x n - B.proj n y := (hsurj n _).choose_spec
  let z : B.pt := e.inv x
  have hz (n : ℕ) : B.proj n z = x n := by
    rw [← he]
    exact congrFun (e.toLinearEquiv.apply_symm_apply x) n
  refine ⟨z, e.toLinearEquiv.injective (funext fun n ↦ ?_)⟩
  change e.hom ((𝟙 B.pt - s) z) n = e.hom y n
  rw [he, he]
  have hn := ConcreteCategory.congr_hom (hs n) z
  simp only [ModuleCat.comp_apply] at hn
  change B.proj n (z - s z) = B.proj n y
  simp only [map_sub, hn, hz, hx, sub_sub_cancel]

end ModuleCat
