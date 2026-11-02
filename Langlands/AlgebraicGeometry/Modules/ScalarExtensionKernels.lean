import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Kernel coefficients under scalar extension from a field -/

noncomputable section
universe u

open CategoryTheory
open scoped TensorProduct ChangeOfRings

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Modules

variable {k K : Type u} [Field k] [Field K] (φ : k →+* K)
  {V W : ModuleCat.{u} k}

/-- The scalar extension of the kernel inside the extended source. -/
def scalarKernelImage (r : V ⟶ W) :
    Submodule K ((ModuleCat.extendScalars φ).obj V) :=
  LinearMap.range ((ModuleCat.extendScalars φ).map
    (ModuleCat.ofHom (LinearMap.ker r.hom).subtype)).hom

/-- Tensoring with a field extension preserves the kernel of a linear map. -/
lemma mem_scalarKernelImage_iff (r : V ⟶ W)
    (a : (ModuleCat.extendScalars φ).obj V) :
    a ∈ scalarKernelImage φ r ↔ (ModuleCat.extendScalars φ).map r a = 0 := by
  let : Module k K := Module.compHom K φ
  have hex := Module.Flat.lTensor_exact K (LinearMap.exact_subtype_ker_map r.hom)
  exact (hex a).symm

/-- A nonzero linear observation on a scalar-extended kernel detects a nonzero
observation on the pullback of one actual kernel vector. -/
lemma exists_kernel_coefficient_of_ne_zero (r : V ⟶ W)
    {V' T : ModuleCat.{u} K}
    (c : (ModuleCat.extendScalars φ).obj V ⟶ V') (q : V' ⟶ T)
    (a : (ModuleCat.extendScalars φ).obj V)
    (ha : (ModuleCat.extendScalars φ).map r a = 0) (hne : q (c a) ≠ 0) :
    ∃ s : V, r s = 0 ∧ q (c ((1 : K) ⊗ₜ[k,φ] s)) ≠ 0 := by
  classical
  let : Module k K := Module.compHom K φ
  obtain ⟨b, hb⟩ := (mem_scalarKernelImage_iff φ r a).mpr ha
  by_contra h
  have hz : ∀ s : LinearMap.ker r.hom,
      q (c ((1 : K) ⊗ₜ[k,φ] (s : V))) = 0 := by
    intro s
    by_contra hs
    exact h ⟨s, s.property, hs⟩
  have hall : ∀ b : K ⊗[k] LinearMap.ker r.hom,
      q (c ((LinearMap.ker r.hom).subtype.lTensor K b)) = 0 := by
    intro b
    induction b using TensorProduct.inductionOn with
    | tmul z s =>
        change q.hom (c.hom (z ⊗ₜ[k,φ] (s : V))) = 0
        have ht : (z ⊗ₜ[k,φ] (s : V) : (ModuleCat.extendScalars φ).obj V) =
            z • ((1 : K) ⊗ₜ[k,φ] (s : V)) := by
          rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
        rw [ht, map_smul, map_smul, hz s, smul_zero]
    | add b₁ b₂ h₁ h₂ =>
        change q.hom (c.hom ((LinearMap.ker r.hom).subtype.lTensor K (b₁ + b₂))) = 0
        rw [map_add, map_add, map_add, h₁, h₂, add_zero]
  apply hne
  rw [← hb]
  exact hall b

end Langlands.AlgebraicGeometry.Modules
