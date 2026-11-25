/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons
import WeilConjectures.AlgebraicGeometry.InvertibleTensorPowerBlockInterchange
import WeilConjectures.AlgebraicGeometry.BoundaryPullbackTensorBraiding
import WeilConjectures.AlgebraicGeometry.BoundaryCoefficientDegreeSplit

/-! # Tensor pairing for the coefficient-degree comparisons

Source: Stacks Project, Tags 01CD and 09MS.
(blueprint: lem-sc-boundary-coefficient-tensor-product).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section

/-- Move the ideal factor to the left and multiply the two tensor degrees.
Source: Stacks Project, Tag 09MS, ideal coefficient tensor multiplication.
(blueprint: lem-sc-boundary-coefficient-tensor-product). -/
def boundaryIdealTensorProduct {X : Scheme.{u}} (J L : X.Modules) (a b : ℕ) :
    L.tensorPow a ⊗ (J ⊗ L.tensorPow b) ⟶ J ⊗ L.tensorPow (a + b) :=
  (α_ _ _ _).inv ≫ (β_ _ _).hom ▷ _ ≫ (α_ _ _ _).hom ≫
    J ◁ (L.tensorPowAddIso a b).inv

private theorem boundaryIdealTensorProduct_interchange {X : Scheme.{u}}
    (J L : X.Modules) [L.IsInvertible] (a b : ℕ) :
    boundaryIdealTensorProduct J L a b =
      (β_ (L.tensorPow a) (J ⊗ L.tensorPow b)).hom ≫
        (α_ J (L.tensorPow b) (L.tensorPow a)).hom ≫
        J ◁ (L.tensorPowAddIso b a).inv ≫
        J ◁ eqToHom (congrArg L.tensorPow (Nat.add_comm b a)) := by
  unfold boundaryIdealTensorProduct
  rw [tensorPowAddIso_inv_block_interchange]
  simp only [whiskerLeft_comp, Category.assoc, BraidedCategory.braiding_tensor_right_hom,
    Iso.inv_hom_id_assoc]

/-- The coefficient comparison repartitions a product into its coefficient and section blocks.
This involves only tensor comparisons on Z, with no kernel, square-zero hypothesis, or lift.

Source: Stacks Project, Tag 01CD (pullback of tensor products), and Tag 09MS,
coherent-equation-ses (tensor powers of the ideal coefficient).
(blueprint: lem-sc-boundary-coefficient-tensor-product).
Proof: Use tensorPowAddIso_inv_block_interchange to interchange the two L blocks.
The braiding hexagon then factors boundaryIdealTensorProduct through braiding the
section block past the entire coefficient block and coefficient-first concatenation.
Combine the arithmetic casts and apply tensorPullback to this factorization.
Apply boundaryCoefficientDegreeIso_split to the coefficient-first concatenation,
and boundaryPullbackTensorIso_braiding to its preceding braiding. This gives the
morphism equality before evaluating on sections. Evaluate it on the inverse
tensorator applied to q tensor s; cancel that tensorator with its inverse.
The braiding section formula interchanges q and s, and tensorHom_app_tmulSection
applies the two remaining comparison maps separately, giving the asserted formula.
The block interchange lemma uses local free generators and sheaf separation;
the coefficient splitting lemma uses induction and monoidal coherence without
invertibility. Zero exponents and empty opens obey these same tensor identities. -/
theorem boundaryCoefficientDegreeIso_tensor_product {X Z : Scheme.{u}} (j : Z ⟶ X)
    (L : X.Modules) [L.IsInvertible] (n e : ℕ) (V : Z.Opens)
    (q : Γ((tensorPullback j).obj (L.tensorPow (n * (e + 1))), V))
    (s : Γ((tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow (n * (0 + 1))), V)) :
    let a := n * (e + 1)
    let b := n * (0 + 1)
    let c := n * ((e + 1) + 1)
    let m := boundaryIdealTensorProduct j.ker.toModules L a b ≫
      j.ker.toModules ◁ (eqToHom (by
        dsimp [a, b, c]
        congr 1
        simp only [Nat.mul_add, Nat.mul_one]) : L.tensorPow (a + b) ⟶ L.tensorPow c)
    (boundaryCoefficientDegreeIso j L n (e + 1)).hom.app V
        (((tensorPullback j).map m).app V
          ((boundaryPullbackTensorIso j (L.tensorPow a)
            (j.ker.toModules ⊗ L.tensorPow b)).inv.app V (tmulSection q s))) =
      tmulSection
        ((ρ_ ((tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n))).hom.app V
          ((boundaryCoefficientDegreeIso j L n 0).hom.app V s))
        ((boundarySectionDegreeIso j L n e).hom.app V q) := by
  dsimp only
  let a := n * (e + 1)
  let b := n * (0 + 1)
  let c := n * ((e + 1) + 1)
  let h : a + b = c := by simp [a, b, c, Nat.mul_add]
  let h' : b + a = c := (Nat.add_comm b a).trans h
  let k : (j.ker.toModules ⊗ L.tensorPow b) ⊗ L.tensorPow a ⟶
      j.ker.toModules ⊗ L.tensorPow c :=
    (α_ _ _ _).hom ≫ j.ker.toModules ◁ (L.tensorPowAddIso b a).inv ≫
      j.ker.toModules ◁ eqToHom (congrArg L.tensorPow h')
  have hprod : boundaryIdealTensorProduct j.ker.toModules L a b ≫
      j.ker.toModules ◁ eqToHom (congrArg L.tensorPow h) =
      (β_ (L.tensorPow a) (j.ker.toModules ⊗ L.tensorPow b)).hom ≫ k := by
    rw [boundaryIdealTensorProduct_interchange]
    simp only [k, Category.assoc, ← whiskerLeft_comp, eqToHom_trans]
  have hsplit := boundaryCoefficientDegreeIso_split j L n e
  change (tensorPullback j).map k ≫
    (boundaryCoefficientDegreeIso j L n (e + 1)).hom = _ at hsplit
  have hmap :
      (tensorPullback j).map (boundaryIdealTensorProduct j.ker.toModules L a b ≫
        j.ker.toModules ◁ eqToHom (congrArg L.tensorPow h)) ≫
          (boundaryCoefficientDegreeIso j L n (e + 1)).hom =
        (boundaryPullbackTensorIso j (L.tensorPow a)
          (j.ker.toModules ⊗ L.tensorPow b)).hom ≫
        (β_ ((tensorPullback j).obj (L.tensorPow a))
          ((tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow b))).hom ≫
        (((boundaryCoefficientDegreeIso j L n 0).hom ≫
          (ρ_ ((tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n))).hom) ⊗ₘ
          (boundarySectionDegreeIso j L n e).hom) := by
    rw [hprod, Functor.map_comp, Category.assoc, hsplit,
      ← Category.assoc, boundaryPullbackTensorIso_braiding, Category.assoc]
  have hv := congrArg (fun f ↦ f.app V
    ((boundaryPullbackTensorIso j (L.tensorPow a)
      (j.ker.toModules ⊗ L.tensorPow b)).inv.app V (tmulSection q s))) hmap
  simp only [Hom.comp_app, ConcreteCategory.comp_apply] at hv
  have hi : (boundaryPullbackTensorIso j (L.tensorPow a)
      (j.ker.toModules ⊗ L.tensorPow b)).hom.app V
        ((boundaryPullbackTensorIso j (L.tensorPow a)
          (j.ker.toModules ⊗ L.tensorPow b)).inv.app V (tmulSection q s)) =
      tmulSection q s := by
    exact inv_app_hom_app_apply_of_iso
      (boundaryPullbackTensorIso j (L.tensorPow a)
        (j.ker.toModules ⊗ L.tensorPow b)).symm (tmulSection q s)
  simp only [tensorPow_zero] at hv
  rw [hi, braiding_hom_app_tmulSection, tensorHom_app_tmulSection] at hv
  simp only [Hom.comp_app, ConcreteCategory.comp_apply] at hv
  dsimp only [a, b, c] at hv
  exact hv

end
end AlgebraicGeometry.Scheme.Modules
