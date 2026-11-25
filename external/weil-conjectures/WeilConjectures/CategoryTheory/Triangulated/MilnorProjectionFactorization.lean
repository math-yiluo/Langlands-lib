/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Surjectivity of the cohomology projection of a derived inverse limit

Source: Stacks Project, Derived Categories, Tag 07KC; More on Algebra, Tag 07KY.
(blueprint: lem-pc-milnor-projection-factorization).
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
noncomputable section

set_option backward.isDefEq.respectTransparency false in
/-- A map with the cohomology projection equations of a Roos triangle is epi.
Source: Stacks Project, Derived Categories, Tag 07KC; More on Algebra, Tag 07KY.
(blueprint: lem-pc-milnor-projection-factorization).

Proof: Tag 07KC makes the product comparison in degree i an isomorphism.
Given an element y of the inverse limit, take its tuple of limit projections
and pull it back along this comparison to x in H^i of the product. The limit
cone equations and the formula for the transition endomorphism show that
H^i(1-s)(x) is zero, by joint injectivity of the cohomology projections.
Exactness of the long cohomology sequence at H^i of the product gives an
antecedent z in H^i(L) under H^i(p). The stipulated projection equations of b
show that b(z) and y have identical limit coordinates. Thus b is surjective,
hence epi in abelian groups. No boundedness or surjective-transition hypothesis
is used. This argument also applies when any of the objects are zero. -/
theorem milnor_projection_epi [HasDerivedCategory.{v} AddCommGrpCat.{u}]
    (i : ℤ) (K : ℕᵒᵖ ⥤ DerivedCategory AddCommGrpCat.{u})
    [HasProduct (fun n : ℕ => K.obj (Opposite.op n))]
    (L : DerivedCategory AddCommGrpCat.{u})
    (p : L ⟶ ∏ᶜ fun n : ℕ => K.obj (Opposite.op n))
    (δ : (∏ᶜ fun n : ℕ => K.obj (Opposite.op n)) ⟶ L⟦(1 : ℤ)⟧)
    (hT : IsDerivedLimitTriangle (fun n => K.map (homOfLE (Nat.le_succ n)).op) L p δ)
    (b : (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj L ⟶
      limit (K ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} i))
    (hπ : ∀ n : ℕ, b ≫ limit.π
      (K ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} i) (Opposite.op n) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map
        (p ≫ Pi.π (fun n : ℕ => K.obj (Opposite.op n)) n)) : Epi b := by
  obtain ⟨hP, h⟩ := derivedCategory_countableProducts_and_towerLimit
    AddCommGrpCat.{u}
  let := hP
  have : PreservesLimitsOfShape (Discrete ℕ)
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i) := h.2.1 ℕ i
  let H := DerivedCategory.homologyFunctor AddCommGrpCat.{u} i
  let P := fun n : ℕ => K.obj (Opposite.op n)
  let c := piComparison H P
  let j := Pi.lift (f := fun n : ℕ => H.obj (P n))
    (fun n : ℕ => limit.π (K ⋙ H) (Opposite.op n))
  have hprod := isLimitOfHasProductOfPreservesLimit H P
  let t := towerTransitionEndomorphism (K := P)
    (fun n => K.map (homOfLE (Nat.le_succ n)).op)
  apply (AddCommGrpCat.epi_iff_surjective b).2
  intro y
  let x := (inv c) (j y)
  have hxπ (n : ℕ) : H.map (Pi.π P n) x = limit.π (K ⋙ H) (Opposite.op n) y := by
    change H.map (Pi.π P n) ((inv c) (j y)) = _
    rw [← ConcreteCategory.comp_apply]
    change (inv (piComparison H P) ≫ H.map (Pi.π P n)) (j y) = _
    rw [inv_piComparison_comp_map_π]
    exact ConcreteCategory.congr_hom
      (Pi.lift_comp_π (fun n : ℕ => limit.π (K ⋙ H) (Opposite.op n)) n) y
  have htπ (n : ℕ) : H.map t ≫ H.map (Pi.π P n) = H.map (Pi.π P n) -
      H.map (Pi.π P (n + 1)) ≫ H.map (K.map (homOfLE (Nat.le_succ n)).op) := by
    simp only [← H.map_comp, t, towerTransitionEndomorphism, towerProductShift,
      Preadditive.sub_comp, Category.id_comp, Pi.lift_comp_π, Functor.map_sub]
  have hxzero : H.map t x = 0 := by
    apply Concrete.isLimit_ext (Discrete.functor (fun n : ℕ => H.obj (P n))) hprod
    intro ⟨n⟩
    change H.map (Pi.π P n) (H.map t x) = H.map (Pi.π P n) 0
    rw [← ConcreteCategory.comp_apply, htπ]
    change H.map (Pi.π P n) x - H.map (K.map (homOfLE (Nat.le_succ n)).op)
      (H.map (Pi.π P (n + 1)) x) = H.map (Pi.π P n) 0
    rw [hxπ, hxπ, map_zero]
    have hw := ConcreteCategory.congr_hom
      (limit.w (K ⋙ H) (homOfLE (Nat.le_succ n)).op) y
    simp only [ConcreteCategory.comp_apply, Functor.comp_map] at hw
    change H.map (K.map (homOfLE (Nat.le_succ n)).op)
      (limit.π (K ⋙ H) (Opposite.op (n + 1)) y) =
      limit.π (K ⋙ H) (Opposite.op n) y at hw
    rw [hw, sub_self]
  have hex := DerivedCategory.HomologySequence.exact₂
    (Pretriangulated.Triangle.mk p t δ) hT i
  obtain ⟨z, hz⟩ := (ShortComplex.ab_exact_iff _).1 hex x hxzero
  refine ⟨z, ?_⟩
  apply Concrete.limit_ext (K ⋙ H)
  intro ⟨n⟩
  have hbπ := ConcreteCategory.congr_hom (hπ n) z
  simp only [ConcreteCategory.comp_apply, Functor.map_comp] at hbπ
  rw [hbπ]
  change H.map (Pi.π P n) (H.map p z) = _
  change H.map p z = x at hz
  rw [hz, hxπ]

end
end CategoryTheory
