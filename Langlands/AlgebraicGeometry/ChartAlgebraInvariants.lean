import Langlands.AlgebraicGeometry.ChartAlgebraCoaction

/-! # Universal chart invariance of coaction-invariant elements -/

noncomputable section
universe u
open CategoryTheory
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.ChartAlgebraDescent.Datum

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (D : Datum A B C)

/-- A coaction-invariant element is fixed by every original chart transition. -/
theorem equiv_tmul_of_coactionMap_eq (c : C)
    (hc : D.coactionMap c = (1 : B) ⊗ₜ[A] c)
    (T : CommAlgCat.{u} (CommRingCat.of A)) (f₁ f₂ : B →ₐ[A] T) :
    D.equiv T f₁ f₂ (letI := f₂.toRingHom.toAlgebra; (1 : T) ⊗ₜ[B] c) =
      (letI := f₁.toRingHom.toAlgebra; (1 : T) ⊗ₜ[B] c) := by
  let := f₁.toRingHom.toAlgebra
  let : IsScalarTower A B T := IsScalarTower.of_algebraMap_eq (fun a => (f₁.commutes a).symm)
  let S : CommAlgCat (CommRingCat.of A) := CommAlgCat.of A (T ⊗[B] C)
  let κ : T ⟶ S := CommAlgCat.ofHom
    ((Algebra.TensorProduct.includeLeft : T →ₐ[B] T ⊗[B] C).restrictScalars A)
  let gC : C →+* S := Algebra.TensorProduct.includeRight.toRingHom
  have hgC : Compatible S (κ.hom.comp f₁) gC := by
    intro b
    exact (Algebra.TensorProduct.includeRight : C →ₐ[B] T ⊗[B] C).commutes b
  let χ : universal (A := A) (B := B) (C := C) ⟶ S := CommAlgCat.ofHom
    (Algebra.TensorProduct.lift (κ.hom.comp f₂)
      ((Algebra.TensorProduct.includeRight : C →ₐ[B] T ⊗[B] C).restrictScalars A)
      (fun _ _ => Commute.all _ _))
  have hχl : χ.hom.comp leftChart = κ.hom.comp f₂ := by
    ext b
    change (κ.hom (f₂ b)) * gC 1 = κ.hom (f₂ b)
    rw [map_one, mul_one]
  have hχr : χ.hom.comp rightChart = κ.hom.comp f₁ := by
    ext b
    change (κ.hom (f₂ 1)) * gC (algebraMap B C b) = κ.hom (f₁ b)
    rw [map_one, map_one, one_mul]
    exact hgC b
  have hχg : χ.hom.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom = gC := by
    ext x
    change κ.hom (f₂ 1) * gC x = gC x
    rw [map_one, map_one, one_mul]
  have hn := D.transportHom_naturality χ leftChart rightChart
    Algebra.TensorProduct.includeRight.toRingHom (fun _ => rfl)
  have hcongr := D.transportHom_congr hχl hχr hχg (fun _ => rfl) hgC
  have he := congrArg (fun f : C →+* S => f c) (hn.trans hcongr)
  change χ.hom (D.coactionMap c) = D.transportHom S (κ.hom.comp f₂) (κ.hom.comp f₁) gC hgC c at he
  rw [hc] at he
  have hχc : χ.hom ((1 : B) ⊗ₜ[A] c) = gC c := by
    change κ.hom (f₂ 1) * gC c = gC c
    rw [map_one, map_one, one_mul]
  rw [hχc] at he
  let gs := pointOfCompatible S (κ.hom.comp f₁) gC hgC
  have heval : ∀ x : Fiber (C := C) T f₁,
      evalEquiv S (κ.hom.comp f₁) gs (tensorMap κ f₁ x) = x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul t z =>
      change (t ⊗ₜ[B] (1 : C)) * ((1 : T) ⊗ₜ[B] z) = t ⊗ₜ[B] z
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hnθ := D.naturality T S κ f₁ f₂
    (letI := f₂.toRingHom.toAlgebra; (1 : T) ⊗ₜ[B] c)
  have heθ := congrArg (evalEquiv S (κ.hom.comp f₁) gs) hnθ
  rw [tensorMap_tmul, map_one, heval] at heθ
  change D.transportHom S (κ.hom.comp f₂) (κ.hom.comp f₁) gC hgC c =
    D.equiv T f₁ f₂ (letI := f₂.toRingHom.toAlgebra; (1 : T) ⊗ₜ[B] c) at heθ
  exact heθ.symm.trans he.symm

end Langlands.AlgebraicGeometry.ChartAlgebraDescent.Datum
