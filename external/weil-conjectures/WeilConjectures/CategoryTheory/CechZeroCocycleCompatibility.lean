/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

@[expose] public section

universe u v

namespace CategoryTheory

open Limits Opposite
open scoped Simplicial

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- A categorical degree-zero Cech cocycle gives compatible local morphisms.
Source: Stacks Project, Cohomology on Sites, Tags 03AM and 03AN.
(blueprint: lem-sc-cech-zero-cocycle-compatibility)

Proof: For indices i and j, project the equation z d^0 = 0 onto the (i,j)
component. The alternating coface differential there is the restriction of
z_j minus the restriction of z_i to the product U_i x_X U_j, with singleton
products identified with U_i and U_j by their projections and diagonal inverses.
Thus the two restrictions are equal. Given a : W -> U_i and b : W -> U_j
with equal composites to X, regard W as an object over X with this common
composite. The product universal property gives a morphism from W to the
(i,j) product with projections a and b. Restrict the component equation along
this morphism. Functoriality and the singleton-product identities give the
claimed compatibility equation. This argument applies to morphisms from
any abelian group E, since the coface calculation is an equality of morphisms.
An empty index type has no i,j, so the statement is vacuous.
-/
theorem cech_zero_cocycle_compatibility
    {C : Type u} [Category.{v} C] [HasFiniteWidePullbacks C]
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{v}) (X : C)
    {ι : Type v} {U : ι → C} (π : ∀ i, U i ⟶ X)
    {E : AddCommGrpCat.{v}}
    (z : E ⟶ ∏ᶜ (fun s : Fin 1 → ι ↦
      P.obj (op (∏ᶜ (fun k ↦ Over.mk (π (s k)))).left)))
    (hz : z ≫ ((cechComplexFunctor (fun i ↦ Over.mk (π i))).obj
      ((Over.forget X).op ⋙ P)).d 0 1 = 0)
    {W : C} {i j : ι} (a : W ⟶ U i) (b : W ⟶ U j)
    (hab : a ≫ π i = b ≫ π j) :
    z ≫ Pi.π (fun s : Fin 1 → ι ↦
      P.obj (op (∏ᶜ (fun k ↦ Over.mk (π (s k)))).left)) (fun _ ↦ i) ≫
        P.map (Pi.lift (fun _ : Fin 1 ↦ 𝟙 (Over.mk (π i)))).left.op ≫ P.map a.op =
    z ≫ Pi.π (fun s : Fin 1 → ι ↦
      P.obj (op (∏ᶜ (fun k ↦ Over.mk (π (s k)))).left)) (fun _ ↦ j) ≫
        P.map (Pi.lift (fun _ : Fin 1 ↦ 𝟙 (Over.mk (π j)))).left.op ≫ P.map b.op := by
  let T := (FormalCoproduct.mk _ (fun i ↦ Over.mk (π i))).cech
  let Q := (FormalCoproduct.cosimplicialObjectFunctor T).obj ((Over.forget X).op ⋙ P)
  change z ≫ (∑ k : Fin 2, (-1 : ℤ) ^ (k : ℕ) • Q.δ k) = 0 at hz
  simp only [Fin.sum_univ_two,
    Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul,
    ← sub_eq_add_neg, Preadditive.comp_sub, sub_eq_zero] at hz
  let t : Fin 2 → ι := Fin.cases i (fun _ ↦ j)
  have h := congrArg (fun f ↦ f ≫ Pi.π (fun s : Fin 2 → ι ↦
    P.obj (op (∏ᶜ (fun k ↦ Over.mk (π (s k)))).left)) t) hz
  dsimp [Q, T, FormalCoproduct.cosimplicialObjectFunctor, FormalCoproduct.evalOp,
    CosimplicialObject.δ,
    FormalCoproduct.cech, FormalCoproduct.mapPower,
    FormalCoproduct.power, SimplexCategory.δ] at h
  erw [Category.assoc, Pi.lift_comp_π, Category.assoc, Pi.lift_comp_π] at h
  change z ≫ Pi.π (fun s : Fin 1 → ι ↦
      P.obj (op (∏ᶜ (fun k ↦ Over.mk (π (s k)))).left))
      (t ∘ ⇑(Fin.succAboveOrderEmb (0 : Fin 2)).toOrderHom) ≫
      P.map (Pi.lift (fun k : Fin 1 ↦ Pi.π
        (fun k : Fin 2 ↦ Over.mk (π (t k)))
        ((Fin.succAboveOrderEmb (0 : Fin 2)).toOrderHom k))).left.op =
    z ≫ Pi.π (fun s : Fin 1 → ι ↦
      P.obj (op (∏ᶜ (fun k ↦ Over.mk (π (s k)))).left))
      (t ∘ ⇑(Fin.succAboveOrderEmb (1 : Fin 2)).toOrderHom) ≫
      P.map (Pi.lift (fun k : Fin 1 ↦ Pi.π
        (fun k : Fin 2 ↦ Over.mk (π (t k)))
        ((Fin.succAboveOrderEmb (1 : Fin 2)).toOrderHom k))).left.op at h
  have h0 : (⇑(Fin.succAboveOrderEmb (0 : Fin 2)).toOrderHom) =
      (fun _ : Fin 1 ↦ (1 : Fin 2)) := by
    funext k
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    rfl
  have h1 : (⇑(Fin.succAboveOrderEmb (1 : Fin 2)).toOrderHom) =
      (fun _ : Fin 1 ↦ (0 : Fin 2)) := by
    funext k
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    rfl
  rw [h0, h1] at h
  dsimp [Function.comp_def, t] at h
  let B := Over.mk (a ≫ π i)
  let aa : B ⟶ Over.mk (π i) := Over.homMk a rfl
  let bb : B ⟶ Over.mk (π j) := Over.homMk b hab.symm
  let l : B ⟶ ∏ᶜ (fun k : Fin 2 ↦ Over.mk (π (t k))) :=
    Pi.lift (Fin.cases aa (fun _ ↦ bb))
  let di : (∏ᶜ (fun k : Fin 2 ↦ Over.mk (π (t k)))) ⟶
      ∏ᶜ (fun _ : Fin 1 ↦ Over.mk (π i)) := Pi.lift (fun _ ↦ Pi.π _ 0)
  let dj : (∏ᶜ (fun k : Fin 2 ↦ Over.mk (π (t k)))) ⟶
      ∏ᶜ (fun _ : Fin 1 ↦ Over.mk (π j)) := Pi.lift (fun _ ↦ Pi.π _ 1)
  let qi : Over.mk (π i) ⟶ ∏ᶜ (fun _ : Fin 1 ↦ Over.mk (π i)) :=
    Pi.lift (fun _ ↦ 𝟙 _)
  let qj : Over.mk (π j) ⟶ ∏ᶜ (fun _ : Fin 1 ↦ Over.mk (π j)) :=
    Pi.lift (fun _ ↦ 𝟙 _)
  have hi : l ≫ di = aa ≫ qi := by
    apply Pi.hom_ext
    intro k
    simp [l, di, qi]
  have hj : l ≫ dj = bb ≫ qj := by
    apply Pi.hom_ext
    intro k
    simp [l, dj, qj]
    rfl
  change z ≫ Pi.π (fun s : Fin 1 → ι ↦
    P.obj (op (∏ᶜ (fun k ↦ Over.mk (π (s k)))).left)) (fun _ ↦ j) ≫
      P.map dj.left.op = z ≫ Pi.π (fun s : Fin 1 → ι ↦
    P.obj (op (∏ᶜ (fun k ↦ Over.mk (π (s k)))).left)) (fun _ ↦ i) ≫
      P.map di.left.op at h
  have hi' : l.left ≫ di.left = a ≫ qi.left := congrArg Over.Hom.left hi
  have hj' : l.left ≫ dj.left = b ≫ qj.left := congrArg Over.Hom.left hj
  have hh := congrArg (fun f ↦ f ≫ P.map l.left.op) h
  simp only [Category.assoc] at hh
  rw [← P.map_comp, ← op_comp, hj'] at hh
  conv at hh => rhs; rw [← P.map_comp, ← op_comp, hi']
  simpa only [op_comp, P.map_comp, Category.assoc, qi, qj] using hh.symm

end CategoryTheory
