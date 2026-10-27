import Langlands.AlgebraicGeometry.Modules.TensorLocalFiniteDecompositionStatement

/-! # Proof of local finite pure-tensor decompositions of sheaf tensor sections -/

noncomputable section

universe u

open CategoryTheory
open scoped BigOperators TensorProduct

namespace Langlands.Scheme.Modules

/-- Every element of an algebraic tensor product is a `Fin n`-indexed sum of pure tensors. -/
lemma exists_fin_sum_tmul {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (x : M ⊗[R] N) :
    ∃ (n : ℕ) (s : Fin n → M) (t : Fin n → N), ∑ i : Fin n, s i ⊗ₜ[R] t i = x := by
  induction x with
  | tmul m n => exact ⟨1, fun _ => m, fun _ => n, by simp⟩
  | add x y hx hy =>
    obtain ⟨n₁, s₁, t₁, h₁⟩ := hx
    obtain ⟨n₂, s₂, t₂, h₂⟩ := hy
    exact ⟨n₁ + n₂, Fin.append s₁ s₂, Fin.append t₁ t₂, by
      simp [Fin.sum_univ_add, h₁, h₂]⟩

/-- Sections of the sheaf tensor are locally finite sums of pure sectionwise tensors. -/
theorem tensorLocalFiniteDecomposition (X : AlgebraicGeometry.Scheme.{u}) :
    TensorLocalFiniteDecompositionStatement X := by
  intro M N U z x hx
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map (tensorSheafifyUnit M N)) := by
    change Presheaf.IsLocallySurjective _ (CategoryTheory.toSheafify _ _)
    infer_instance
  obtain ⟨V, f, ⟨w, hw⟩, hxV⟩ :=
    Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map (tensorSheafifyUnit M N)) (U := Opposite.op U) z
      x hx
  obtain ⟨n, s, t, rfl⟩ := exists_fin_sum_tmul w
  exact ⟨V, leOfHom f, hxV, n, s, t, hw⟩

end Langlands.Scheme.Modules
