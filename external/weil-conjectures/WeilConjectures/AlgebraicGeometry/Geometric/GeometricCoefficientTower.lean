/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Homology.CochainCompositeConstruction.CochainCompositeAlgebraic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal

/-! # Explicit transport of a coefficient tower by inverse image

Source: Zheng Construction 4.1; Stacks 03D2.
(blueprint: lem-coef-geometric-coefficient-tower)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe c v r
open CategoryTheory CategoryTheory.Limits
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

attribute [local irreducible] SheafOfModules.CochainCompositeConstruction.ringImage
  SheafOfModules.CochainCompositeConstruction.algebraicImage

/-- A coefficient tower and its algebraic inverse images are transported explicitly.
Source: Zheng Construction 4.1; Stacks 03D2.
(blueprint: lem-coef-geometric-coefficient-tower).

Proof: transport each ring object and its module operations by finite products,
using the actual ringImage and algebraicImage constructions. For a transition,
compose its transported underlying map with the fixed ring-underlying isomorphism.
Its addition, multiplication and unit graphs are preserved: first apply the original
ring homomorphism to the graph equation and then the algebraic inverse-image graph
law at the next level. The structuralMap lemma bundles this map into a ring-sheaf
morphism. Choose that morphism, whose underlying map is specified uniquely. Its
specified underlying equation and cancellation of the ring-underlying isomorphism
give compatibility. No existence theorem with an unspecified object is used in a
definition. -/
theorem geometricCoefficientTower
    {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
    (J' : GrothendieckTopology C')
    (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
    [PreservesFiniteLimits uInv] :
    ∃ (F : ℕ → Sheaf J' CommRingCat.{max c v r})
      (σ : ∀ n : ℕ, F (n + 1) ⟶ F n)
      (I : ∀ n : ℕ, SheafOfModules.AlgebraicInverseImage uInv (B n) (F n)),
      ∀ n : ℕ,
        uInv.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{max c v r})).map
            (τ n)) ≫ (I n).ringUnderlying.hom =
          (I (n + 1)).ringUnderlying.hom ≫
            (sheafCompose J' (CategoryTheory.forget CommRingCat.{max c v r})).map (σ n) := by
  classical
  let : uInv.Braided := Functor.Braided.ofChosenFiniteProducts uInv
  let F (n : ℕ) := SheafOfModules.CochainCompositeConstruction.ringImage uInv (B n)
  let I (n : ℕ) := SheafOfModules.CochainCompositeConstruction.algebraicImage uInv (B n)
  let forgetR := sheafCompose J (CategoryTheory.forget CommRingCat.{max c v r})
  let forgetF := sheafCompose J' (CategoryTheory.forget CommRingCat.{max c v r})
  have maps (n : ℕ) : ∃ f : F (n + 1) ⟶ F n,
      forgetF.map f = (I (n + 1)).ringUnderlying.inv ≫
        (uInv.map (forgetR.map (τ n)) ≫ (I n).ringUnderlying.hom) := by
    apply SheafOfModules.CochainCompositeConstruction.structuralMap
      uInv (B (n + 1)) (F n) (F (n + 1)) (I (n + 1))
      (uInv.map (forgetR.map (τ n)) ≫ (I n).ringUnderlying.hom)
    · intro Z x y z hz
      have h := (I n).ringAdd Z (x ≫ forgetR.map (τ n))
        (y ≫ forgetR.map (τ n)) (z ≫ forgetR.map (τ n)) (by
          intro U t
          change (τ n).hom.app U (z.hom.app U t) =
            (τ n).hom.app U (x.hom.app U t) + (τ n).hom.app U (y.hom.app U t)
          rw [hz U t]
          exact map_add _ _ _)
      simpa only [F, uInv.map_comp, ObjectProperty.FullSubcategory.comp_hom,
        NatTrans.comp_app, types_comp_apply, id_eq, HAdd.hAdd, HMul.hMul] using h
    · intro Z x y z hz
      have h := (I n).ringMul Z (x ≫ forgetR.map (τ n))
        (y ≫ forgetR.map (τ n)) (z ≫ forgetR.map (τ n)) (by
          intro U t
          change (τ n).hom.app U (z.hom.app U t) =
            (τ n).hom.app U (x.hom.app U t) * (τ n).hom.app U (y.hom.app U t)
          rw [hz U t]
          exact map_mul _ _ _)
      simpa only [F, uInv.map_comp, ObjectProperty.FullSubcategory.comp_hom,
        NatTrans.comp_app, types_comp_apply, id_eq, HAdd.hAdd, HMul.hMul] using h
    · intro Z z hz
      have h := (I n).ringOne Z (z ≫ forgetR.map (τ n)) (by
        intro U t
        change (τ n).hom.app U (z.hom.app U t) = 1
        rw [hz U t]
        exact map_one _)
      simpa only [F, uInv.map_comp, ObjectProperty.FullSubcategory.comp_hom,
        NatTrans.comp_app, types_comp_apply, id_eq, HAdd.hAdd, HMul.hMul] using h
  let σ (n : ℕ) := (maps n).choose
  refine ⟨F, σ, I, ?_⟩
  intro n
  rw [(maps n).choose_spec]
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rfl

end WeilConjectures.SemilinearSections
