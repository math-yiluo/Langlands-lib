import Langlands.CommutativeAlgebra.HenselianSections
import Langlands.TauCeti.RingTheory.WeilRestriction.Smooth

/-! # Smooth lifting along a finite projective algebra over a Henselian ring -/

universe u

open scoped TensorProduct

noncomputable section

namespace Langlands.CommutativeAlgebra.HenselianSections

/-- A point of a smooth algebra over a finite projective algebra lifts from the
base residue fibre, by applying Henselian lifting to its Weil restriction. -/
theorem exists_lift_of_finite_projective_smooth
    {R k B C : Type u} [CommRing R] [HenselianLocalRing R]
    [Field k] [Algebra R k] [CommRing B] [Algebra R B]
    [Module.Finite R B] [Module.Projective R B]
    [CommRing C] [Algebra B C] [Algebra.Smooth B C]
    (hk : Function.Surjective (algebraMap R k))
    (φ : C →ₐ[B] B ⊗[R] k) :
    ∃ σ : C →ₐ[B] B, (Algebra.ofId B (B ⊗[R] k)).comp σ = φ := by
  let W := TauCeti.Algebra.WeilRestriction R B C
  let ψ : W →ₐ[R] k :=
    (TauCeti.Algebra.WeilRestriction.homEquiv R B C k).symm φ
  obtain ⟨τ, hτ⟩ := exists_lift_of_smooth hk ψ
  let σ₀ : C →ₐ[B] B ⊗[R] R :=
    TauCeti.Algebra.WeilRestriction.homEquiv R B C R τ
  have hσ₀ :
      (Algebra.TensorProduct.lTensor B (Algebra.ofId R k)).comp σ₀ = φ := by
    rw [← TauCeti.Algebra.WeilRestriction.homEquiv_comp, hτ]
    exact Equiv.apply_symm_apply _ φ
  have htensor :
      (Algebra.ofId B (B ⊗[R] k)).comp
          (Algebra.TensorProduct.rid R B B).toAlgHom =
        Algebra.TensorProduct.lTensor B (Algebra.ofId R k) := by
    ext
  refine ⟨(Algebra.TensorProduct.rid R B B).toAlgHom.comp σ₀, ?_⟩
  rw [← AlgHom.comp_assoc, htensor]
  exact hσ₀

/-- Choose the lift supplied by finite projective Weil restriction. -/
def finiteProjectiveSmoothLift
    {R k B C : Type u} [CommRing R] [HenselianLocalRing R]
    [Field k] [Algebra R k] [CommRing B] [Algebra R B]
    [Module.Finite R B] [Module.Projective R B]
    [CommRing C] [Algebra B C] [Algebra.Smooth B C]
    (hk : Function.Surjective (algebraMap R k))
    (φ : C →ₐ[B] B ⊗[R] k) : C →ₐ[B] B :=
  Classical.choose (exists_lift_of_finite_projective_smooth hk φ)

/-- The chosen lift reduces to the prescribed point. -/
theorem finiteProjectiveSmoothLift_spec
    {R k B C : Type u} [CommRing R] [HenselianLocalRing R]
    [Field k] [Algebra R k] [CommRing B] [Algebra R B]
    [Module.Finite R B] [Module.Projective R B]
    [CommRing C] [Algebra B C] [Algebra.Smooth B C]
    (hk : Function.Surjective (algebraMap R k))
    (φ : C →ₐ[B] B ⊗[R] k) :
    (Algebra.ofId B (B ⊗[R] k)).comp (finiteProjectiveSmoothLift hk φ) = φ :=
  Classical.choose_spec (exists_lift_of_finite_projective_smooth hk φ)

end Langlands.CommutativeAlgebra.HenselianSections
