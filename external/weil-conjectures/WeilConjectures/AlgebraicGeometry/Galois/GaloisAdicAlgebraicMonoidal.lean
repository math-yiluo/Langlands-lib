/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Galois.GaloisAdicDataFromFinite
import WeilConjectures.AlgebraicGeometry.Galois.GaloisAdicRationalProperties
import WeilConjectures.AlgebraicGeometry.Galois.GaloisAdicDataFromFinite
import Mathlib.LinearAlgebra.TensorProduct.Tower

set_option linter.privateModule false

/-! # Tensor and unit comparisons for algebraic l-adic sheaves -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite
open scoped TensorProduct MonoidalCategory

namespace AlgebraicGeometry.Scheme

private def scalarRep
    (E L : Type (u + 1)) [Field E] [Field L] [Algebra E L]
    {G : Type u} [Group G] (X : Rep.{u + 1} E G) : Rep.{u + 1} L G :=
  Rep.of ((Module.End.baseChangeHom E L X.V).toMonoidHom.comp X.ρ)

private def scalarTowerIso
    (E L Q : Type (u + 1)) [Field E] [Field L] [Field Q]
    [Algebra E L] [Algebra E Q] [Algebra L Q] [IsScalarTower E L Q]
    {G : Type u} [Group G] (X : Rep.{u + 1} E G) :
    scalarRep L Q (scalarRep E L X) ≅ scalarRep E Q X := by
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange E L Q Q X.V
  exact Rep.mkIso
    { toLinearEquiv := e
      isIntertwining' := fun g ↦ by
        apply TensorProduct.AlgebraTensorModule.ext
        intro a v
        induction v using TensorProduct.inductionOn with
        | add x z hx hz => simp only [TensorProduct.tmul_add, map_add, hx, hz]
        | tmul b x =>
          change e (a ⊗ₜ[L] (b ⊗ₜ[E] X.ρ g x)) =
            (LinearMap.baseChange Q (X.ρ g)) (e (a ⊗ₜ[L] (b ⊗ₜ[E] x)))
          simp only [e, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
            LinearMap.baseChange_tmul] }

private noncomputable def scalarTensorIso
    (E Q : Type (u + 1)) [Field E] [Field Q] [Algebra E Q]
    {G : Type u} [Group G] (X Y : Rep.{u + 1} E G) :
    scalarRep E Q X ⊗ scalarRep E Q Y ≅ scalarRep E Q (X ⊗ Y) := by
  let e := (TensorProduct.AlgebraTensorModule.distribBaseChange E Q X.V Y.V).symm
  exact Rep.mkIso
    { toLinearEquiv := e
      isIntertwining' := fun g ↦ by
        apply TensorProduct.AlgebraTensorModule.ext
        intro v w
        induction v using TensorProduct.inductionOn generalizing w with
        | add x z hx hz => simp only [map_add, TensorProduct.add_tmul, hx, hz]
        | tmul a x =>
          induction w using TensorProduct.inductionOn with
          | add y z hy hz => simp only [map_add, TensorProduct.tmul_add, hy, hz]
          | tmul b y =>
            change e ((a ⊗ₜ[E] X.ρ g x) ⊗ₜ[Q] (b ⊗ₜ[E] Y.ρ g y)) =
              (LinearMap.baseChange Q ((X.ρ.tprod Y.ρ) g))
                (e ((a ⊗ₜ[E] x) ⊗ₜ[Q] (b ⊗ₜ[E] y)))
            simp only [e, TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul,
              LinearMap.baseChange_tmul, Representation.tprod_apply, TensorProduct.map_tmul] }

end AlgebraicGeometry.Scheme
