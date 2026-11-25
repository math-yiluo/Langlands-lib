/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Additive

/-! # Semilinear transport of ordinary tensor complexes

Source: Mathlib `TensorProduct.congr` and `HomologicalComplex.Hom.isoOfComponents`.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry

/-- Compatible ring equivalences and a semilinear chain isomorphism induce an
additive isomorphism of scalar-extended complexes.

Proof: view eC as an eA-semilinear equivalence after restricting scalars along
f0 and f1. In each degree alpha is also an eA-semilinear equivalence. Apply
TensorProduct.congr to these two equivalences. On pure tensors the resulting
map is eC(c) tensor alpha(q). The chain identity for alpha proves compatibility
with differentials on pure tensors, and tensor induction proves it everywhere.
The inverse is the tensor of the inverse equivalences; TensorProduct.congr
already verifies its inverse equations. No flatness or nonzero-ring assumption
is used.
Source: Mathlib `TensorProduct.congr`, `ModuleCat.ExtendScalars.map_tmul`, and
`HomologicalComplex.Hom.isoOfComponents`.
(blueprint: lem-pc-semilinear-tensor-complex-iso). -/
theorem exists_semilinearTensorComplexIso
    {A₀ A₁ C₀ C₁ : Type u}
    [CommRing A₀] [CommRing A₁] [CommRing C₀] [CommRing C₁]
    (f₀ : A₀ →+* C₀) (f₁ : A₁ →+* C₁)
    (eA : A₀ ≃+* A₁) (eC : C₀ ≃+* C₁)
    (h : eC.toRingHom.comp f₀ = f₁.comp eA.toRingHom)
    (K₀ : CochainComplex (ModuleCat.{u} A₀) ℤ)
    (K₁ : CochainComplex (ModuleCat.{u} A₁) ℤ)
    (α : ((forget₂ (ModuleCat.{u} A₀) AddCommGrpCat.{u}).mapHomologicalComplex
        (.up ℤ)).obj K₀ ≅
      ((forget₂ (ModuleCat.{u} A₁) AddCommGrpCat.{u}).mapHomologicalComplex
        (.up ℤ)).obj K₁)
    (hα : ∀ (n : ℤ) (a : A₀) (q : K₀.X n),
      α.hom.f n (a • q) = eA a • (show K₁.X n from α.hom.f n q)) :
    ∃ τ : ((forget₂ (ModuleCat.{u} C₀) AddCommGrpCat.{u}).mapHomologicalComplex
        (.up ℤ)).obj (((ModuleCat.extendScalars f₀).mapHomologicalComplex (.up ℤ)).obj K₀) ≅
      ((forget₂ (ModuleCat.{u} C₁) AddCommGrpCat.{u}).mapHomologicalComplex
        (.up ℤ)).obj (((ModuleCat.extendScalars f₁).mapHomologicalComplex (.up ℤ)).obj K₁),
      ∀ (n : ℤ) (c : C₀) (q : K₀.X n),
        τ.hom.f n (c ⊗ₜ[A₀,f₀] q) =
          eC c ⊗ₜ[A₁,f₁] (show K₁.X n from α.hom.f n q) := by
  classical
  let : RingHomInvPair eA.toRingHom eA.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv eA
  let : RingHomInvPair eA.symm.toRingHom eA.toRingHom :=
    RingHomInvPair.of_ringEquiv_symm eA
  let ec : LinearEquiv eA.toRingHom (σ' := eA.symm.toRingHom)
      ((ModuleCat.restrictScalars f₀).obj (ModuleCat.of C₀ C₀))
      ((ModuleCat.restrictScalars f₁).obj (ModuleCat.of C₁ C₁)) :=
    { eC.toAddEquiv with
      map_smul' := fun a c => by
        change eC (f₀ a * (show C₀ from c)) = f₁ (eA a) * eC c
        rw [map_mul]
        exact congrArg (fun x => x * eC c) (DFunLike.congr_fun h a) }
  let ea (n : ℤ) : LinearEquiv eA.toRingHom (σ' := eA.symm.toRingHom)
      (K₀.X n) (K₁.X n) :=
    { (HomologicalComplex.Hom.isoApp α n).addCommGroupIsoToAddEquiv with
      map_smul' := hα n }
  let et (n : ℤ) := TensorProduct.congr ec (ea n)
  let τ : ((forget₂ (ModuleCat.{u} C₀) AddCommGrpCat.{u}).mapHomologicalComplex
      (.up ℤ)).obj (((ModuleCat.extendScalars f₀).mapHomologicalComplex (.up ℤ)).obj K₀) ≅
      ((forget₂ (ModuleCat.{u} C₁) AddCommGrpCat.{u}).mapHomologicalComplex
        (.up ℤ)).obj (((ModuleCat.extendScalars f₁).mapHomologicalComplex (.up ℤ)).obj K₁) :=
    HomologicalComplex.Hom.isoOfComponents
    (fun n => (et n).toAddEquiv.toAddCommGrpIso) (by
      intro i j hij
      ext x
      induction x using TensorProduct.inductionOn with
      | tmul c q =>
        change eC c ⊗ₜ[A₁,f₁] (K₁.d i j (show K₁.X i from α.hom.f i q)) =
            eC c ⊗ₜ[A₁,f₁] (show K₁.X j from α.hom.f j (K₀.d i j q))
        exact congrArg (fun q => eC c ⊗ₜ[A₁,f₁] q)
          (ConcreteCategory.congr_hom (α.hom.comm i j) q)
      | add x y hx hy => simp only [map_add, hx, hy])
  exact ⟨τ, fun _ _ _ => rfl⟩

end AlgebraicGeometry
