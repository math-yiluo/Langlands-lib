/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation
public import WeilConjectures.Mathlib.Algebra.Algebra.Subalgebra.Tower

/-!
# Finitely many étale algebras descend to a common finitely generated subring

A first step towards descending a presentation of a constructible sheaf on `Spec A`
(Stacks 095N) to a Noetherian stage, as needed for Stacks 01ZA: finitely many étale `A`-algebras
are base changes of étale algebras over one finitely generated subring of `A`
(`AlgebraicGeometry.exists_finset_algEquiv_tensorProduct_of_etale_fin`).
-/

@[expose] public section

universe u

open TensorProduct

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A]

/-- **Finitely many étale algebras descend to one finitely generated subring.** -/
theorem exists_finset_algEquiv_tensorProduct_of_etale_fin {m : ℕ} (B : Fin m → Type u)
    [∀ k, CommRing (B k)] [∀ k, Algebra A (B k)] [∀ k, Algebra.Etale A (B k)] :
    ∃ (F : Finset A) (B₀ : Fin m → Type u) (_ : ∀ k, CommRing (B₀ k))
      (_ : ∀ k, Algebra (Algebra.adjoin ℤ (F : Set A)) (B₀ k)),
      ∀ k, Algebra.Etale (Algebra.adjoin ℤ (F : Set A)) (B₀ k) ∧
        Nonempty (A ⊗[Algebra.adjoin ℤ (F : Set A)] B₀ k ≃ₐ[A] B k) := by
  classical
  choose F B₀ _ _ hE he using fun k ↦ exists_finset_algEquiv_tensorProduct_of_etale (A := A) (B k)
  let G : Finset A := Finset.univ.biUnion F
  have hle (k : Fin m) : Algebra.adjoin ℤ (F k : Set A) ≤ Algebra.adjoin ℤ (G : Set A) :=
    Algebra.adjoin_mono (by
      intro a ha
      exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, ha⟩)
  let A₀ := Algebra.adjoin ℤ (G : Set A)
  let (k : Fin m) : Algebra (Algebra.adjoin ℤ (F k : Set A)) A₀ :=
    (Subalgebra.inclusion (hle k)).toAlgebra
  have (k : Fin m) : IsScalarTower (Algebra.adjoin ℤ (F k : Set A)) A₀ A :=
    Subalgebra.isScalarTower_inclusion (hle k)
  refine ⟨G, fun k ↦ A₀ ⊗[Algebra.adjoin ℤ (F k : Set A)] B₀ k, fun _ ↦ inferInstance,
    fun _ ↦ inferInstance, fun k ↦ ⟨inferInstance, ?_⟩⟩
  obtain ⟨e⟩ := he k
  exact ⟨(Algebra.TensorProduct.cancelBaseChange (Algebra.adjoin ℤ (F k : Set A)) A₀ A A
    (B₀ k)).trans e⟩

end AlgebraicGeometry
