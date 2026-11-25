/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection

/-! # Universal property of the change-of-rings balancing map

Source: Stacks Project, Morphisms, proof of Lemma 01SB; Sheaves, Lemma 0089.
(blueprint: lem-weil-pbc-change-of-rings-tensor-balancing-universal).
-/

@[expose] public section

universe u

open CategoryTheory Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

set_option hygiene false in
local notation "𝓡" S => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj S
set_option hygiene false in
local notation "𝓻" a => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map a

/-- Uniqueness clause for the balancing factorization.
Source: Stacks Project, Morphisms, proof of Lemma 01SB.
(blueprint: aux-lem-weil-pbc-change-of-rings-tensor-balancing-universal-unique)
Two factorizations agree on pure tensors, which generate sectionwise, and hence agree
after sheafification. -/
theorem changeOfRings_tensor_balancing_universal_unique (Y : Scheme.{u})
    (B C : Y.CommAlgebraSheaf) (φ : B ⟶ C)
    (P : SheafOfModules.{u} (𝓡 B.right)) :
    let P₀ := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P
    let S := tensorObj C.toModule P₀
    let T := (SheafOfModules.restrictScalars (𝓻 C.hom)).obj
      (SheafOfModules.changeOfRings.{u, u, u} φ.right P)
    ∀ (a d : tensorObj B.toModule S ⟶ S) (g : S ⟶ T),
      (∀ (W : Y.Opens) (b : B.right.obj.obj (op W))
          (c : C.right.obj.obj (op W)) (p : P.val.obj (op W)),
        a.app W (tmulSection (M := B.toModule)
          b (tmulSection (M := C.toModule) (N := P₀) c p)) =
          tmulSection (M := C.toModule) (N := P₀) c (b • p)) →
      (∀ (W : Y.Opens) (b : B.right.obj.obj (op W))
          (c : C.right.obj.obj (op W)) (p : P.val.obj (op W)),
        d.app W (tmulSection (M := B.toModule)
          b (tmulSection (M := C.toModule) (N := P₀) c p)) =
          tmulSection (M := C.toModule) (N := P₀)
            (φ.right.hom.app (op W) b * c) p) →
      (∀ (W : Y.Opens) (c : C.right.obj.obj (op W)) (p : P.val.obj (op W)),
        g.app W (tmulSection (M := C.toModule) (N := P₀) c p) =
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 (𝓡 C.right).obj)).unit.app
            (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ.right P)).app
              (op W))
              (c ⊗ₜ[B.right.obj.obj (op W), (φ.right.hom.app (op W)).hom] p)) →
      ∀ (Q : Y.Modules) (f : S ⟶ Q) (t₁ t₂ : T ⟶ Q),
        g ≫ t₁ = f → g ≫ t₂ = f → t₁ = t₂ := by
  dsimp
  intro a d g ha hd hg Q f t₁ t₂ ht₁ ht₂
  apply SheafOfModules.hom_ext
  apply (PresheafOfModules.toPresheaf _).map_injective
  apply CategoryTheory.sheafify_hom_ext (Opens.grothendieckTopology Y) _ _ Q.isSheaf
  ext W x
  induction x using TensorProduct.inductionOn with
  | tmul c p =>
    have hcomp := congrArg (fun k => k.val.app W
      (tmulSection (M := C.toModule)
        (N := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P) c p))
      (ht₁.trans ht₂.symm)
    change (t₁.val.app W) (g.val.app W (tmulSection
      (M := C.toModule) (N := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P) c p)) =
      (t₂.val.app W) (g.val.app W (tmulSection
      (M := C.toModule) (N := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P) c p)) at hcomp
    have hgg := hg W.unop c p
    change (g.val.app W) (tmulSection
      (M := C.toModule) (N := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P) c p) = _ at hgg
    rw [hgg] at hcomp
    exact hcomp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy


end AlgebraicGeometry.Scheme.Modules
