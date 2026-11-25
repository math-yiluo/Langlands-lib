/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeComparison
import Mathlib.Algebra.BigOperators.Pi
import WeilConjectures.AlgebraicGeometry.EtaleSingletonTensorCechNormalizedCoface

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

noncomputable section

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem amitsurMap_tprod {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B] (n : ℕ) (j : Fin (n + 2)) (b : Fin (n + 1) → B) :
    Algebra.TensorProduct.amitsurMap A B j.succAbove (PiTensorProduct.tprod A b) =
      PiTensorProduct.tprod A (j.insertNth 1 b) := by
  have hp (x : Fin (n + 1) → B) :
      PiTensorProduct.tprod A x =
        ∏ i, PiTensorProduct.singleAlgHom (R := A) (A := fun _ ↦ B) i (x i) := by
    simp only [PiTensorProduct.singleAlgHom_apply]
    rw [← PiTensorProduct.tprod_prod]
    congr 1
    exact (Finset.univ_prod_mulSingle x).symm
  rw [hp, map_prod]
  simp only [← AlgHom.comp_apply, Algebra.TensorProduct.amitsurMap_comp_singleAlgHom]
  simp only [PiTensorProduct.singleAlgHom_apply]
  rw [← PiTensorProduct.tprod_prod]
  congr 1
  funext k
  refine Fin.succAboveCases j ?_ (fun i ↦ ?_) k
  · simp
  · simp [Pi.mulSingle_apply]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Fixed-degree pure-tensor coface compatibility.
Source: Stacks Project, Tag 03P2, affine-case tensor differential formula.
(blueprint: new-etale-affine-singleton-tensor-pure-coface-fixed)

This is the fixed `(n,j)` component of the pure-tensor coface equation.  It
is obtained by evaluating the singleton product at its unique tuple, using the
normalization formula for `e n` and `e (n+1)`, and the functoriality of section
restriction.  The inserted Amitsur factor is the unit, while all retained
factors are carried by the corresponding product projections.
-/
theorem singletonTensorDegreeComparison_pure_coface_fixed
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U W : X.Etale) (g : W ⟶ U)
    (e : ∀ n : ℕ, (singletonTensorAmitsur X F U W g).X n ≅
      (singletonTensorCech X F U W g).X n)
    (he : ∀ n, IsSingletonTensorDegreeComparison X F U W g n (e n))
    (n : ℕ) (j : Fin (n + 2))
      (m : Γ((Modules.tensorPullback U.hom).obj F, ⊤))
      (b : Fin (n + 1) → Γ(W.left, ⊤)) :
    letI : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
    ((e n).hom ≫ (singletonTensorCechCosimplicial X F U W g).δ j)
        (ULift.up (m ⊗ₜ[Γ(U.left, ⊤)] PiTensorProduct.tprod Γ(U.left, ⊤) b)) =
      ((singletonTensorForget U.left).map
        ((Algebra.TensorProduct.amitsurCosimplicialObject Γ(U.left, ⊤) Γ(W.left, ⊤)
          Γ((Modules.tensorPullback U.hom).obj F, ⊤)).δ j) ≫ (e (n + 1)).hom)
            (ULift.up (m ⊗ₜ[Γ(U.left, ⊤)] PiTensorProduct.tprod Γ(U.left, ⊤) b)) := by
  classical
  let : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
  have hr : ((singletonTensorForget U.left).map
      ((Algebra.TensorProduct.amitsurCosimplicialObject Γ(U.left, ⊤) Γ(W.left, ⊤)
        Γ((Modules.tensorPullback U.hom).obj F, ⊤)).δ j))
      (ULift.up (m ⊗ₜ[Γ(U.left, ⊤)] PiTensorProduct.tprod Γ(U.left, ⊤) b)) =
      ULift.up (m ⊗ₜ[Γ(U.left, ⊤)]
        PiTensorProduct.tprod Γ(U.left, ⊤) (j.insertNth 1 b)) := by
    apply ULift.ext
    change ((Algebra.TensorProduct.amitsurCosimplicialObject _ _ _).δ j).hom
      (m ⊗ₜ[Γ(U.left, ⊤)] PiTensorProduct.tprod Γ(U.left, ⊤) b) = _
    erw [Algebra.TensorProduct.amitsurCosimplicialObject_δ_hom,
      LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, amitsurMap_tprod]
  change (singletonTensorCechCosimplicial X F U W g).δ j
    ((e n).hom (ULift.up
      (m ⊗ₜ[Γ(U.left, ⊤)] PiTensorProduct.tprod Γ(U.left, ⊤) b))) =
    (e (n + 1)).hom (((singletonTensorForget U.left).map
      ((Algebra.TensorProduct.amitsurCosimplicialObject Γ(U.left, ⊤) Γ(W.left, ⊤)
        Γ((Modules.tensorPullback U.hom).obj F, ⊤)).δ j))
      (ULift.up (m ⊗ₜ[Γ(U.left, ⊤)] PiTensorProduct.tprod Γ(U.left, ⊤) b)))
  rw [hr]
  apply singletonTensorCech_normalized_coface X F U W g n j (e n).hom
    (e (n + 1)).hom ?_ ?_ m b
  · exact he n
  · exact he (n + 1)

end
end AlgebraicGeometry.Scheme
