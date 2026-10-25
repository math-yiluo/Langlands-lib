/-
Copyright (c) 2025 Madison Crim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Madison Crim

Modified by Worker 146 (2026): adapted the finite-presentation argument of
Imperial FLT commit 923d45174c500aa1d994ba973bac38ea39eacbf7,
FLT/DedekindDomain/FiniteAdeleRing/TensorPi.lean:199-270.
Use Mathlib's finite presentation and right-exact five lemma. Replace the
source's finite-free helper definitions (lines 59-175) by scalar tensor
and finite-product equivalences. Prove the published proposition directly,
with four independent universes; do not package a new equivalence.
The upstream license is at licenses/ImperialCollegeLondon-FLT/LICENSE.
-/
import Langlands.LinearAlgebra.RestrictedProduct.TensorPiStatement
import Mathlib.Algebra.FiveLemma

namespace RestrictedProduct

open TensorProduct Function

universe uR uM uι uN

private theorem piRightHom_fin_bijective
    (R : Type uR) [CommRing R] {ι : Type uι} (N : ι → Type uN)
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)] (n : ℕ) :
    Bijective (piRightHom R R (Fin n → R) N) := by
  let e₁ := TensorProduct.comm R (Fin n → R) (∀ i, N i) ≪≫ₗ
    piScalarRight R R (∀ i, N i) (Fin n)
  let e₂ (i : ι) := TensorProduct.comm R (Fin n → R) (N i) ≪≫ₗ
    piScalarRight R R (N i) (Fin n)
  let flip : (Fin n → ∀ i, N i) ≃ₗ[R] (∀ i, Fin n → N i) :=
    { Equiv.piComm (fun (_ : Fin n) i ↦ N i) with
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let E := e₁ ≪≫ₗ flip ≪≫ₗ LinearEquiv.piCongrRight (fun i ↦ (e₂ i).symm)
  have hE : E.toLinearMap = piRightHom R R (Fin n → R) N := by
    apply TensorProduct.ext'
    intro x y
    ext i
    apply (e₂ i).injective
    simp [E, flip, e₁, e₂, piScalarRight_apply, piScalarRightHom_tmul]
    rfl
  rw [← hE]
  exact E.bijective

/-- Tensoring a finitely presented module commutes with any product. -/
theorem tensorPiComparison_proof : TensorPiComparison.{uR, uM, uι, uN} := by
  intro R M _ _ _ _ ι N _ _
  obtain ⟨n, m, g, f, surj, exact⟩ := Module.FinitePresentation.exists_fin' R M
  let i₁ := piRightHom R R (Fin m → R) N
  let i₂ := piRightHom R R (Fin n → R) N
  let i₃ := piRightHom R R M N
  let f₁ := f.rTensor (∀ i, N i)
  let f₂ := g.rTensor (∀ i, N i)
  let g₁ : (∀ i, (Fin m → R) ⊗[R] N i) →ₗ[R] ∀ i, (Fin n → R) ⊗[R] N i :=
    LinearMap.pi (fun i ↦ f.rTensor (N i) ∘ₗ LinearMap.proj i)
  let g₂ : (∀ i, (Fin n → R) ⊗[R] N i) →ₗ[R] ∀ i, M ⊗[R] N i :=
    LinearMap.pi (fun i ↦ g.rTensor (N i) ∘ₗ LinearMap.proj i)
  have hc₁ : g₁ ∘ₗ i₁ = i₂ ∘ₗ f₁ := by
    apply TensorProduct.ext'
    intro x y
    ext i
    simp [g₁, i₁, i₂, f₁]
  have hc₂ : g₂ ∘ₗ i₂ = i₃ ∘ₗ f₂ := by
    apply TensorProduct.ext'
    intro x y
    ext i
    simp [g₂, i₂, i₃, f₂]
  have hg₁ : Exact g₁ g₂ := by
    intro y
    rw [Set.mem_range]
    have h (i : ι) : Exact (f.rTensor (N i)) (g.rTensor (N i)) :=
      rTensor_exact (N i) exact surj
    constructor
    · intro hy
      choose x hx using fun i ↦ (h i (y i)).mp (congrFun hy i)
      exact ⟨x, funext hx⟩
    · rintro ⟨x, hx⟩
      exact funext fun i ↦ (h i (y i)).mpr ⟨x i, congrFun hx i⟩
  have hg₂ : Surjective g₂ := by
    intro y
    choose x hx using fun i ↦ LinearMap.rTensor_surjective (N i) surj (y i)
    exact ⟨x, funext hx⟩
  exact LinearMap.bijective_of_surjective_of_bijective_of_right_exact
    f₁ f₂ g₁ g₂ i₁ i₂ i₃ hc₁ hc₂ (rTensor_exact _ exact surj) hg₁
    (piRightHom_fin_bijective R N m).surjective (piRightHom_fin_bijective R N n)
    (LinearMap.rTensor_surjective _ surj) hg₂

end RestrictedProduct
