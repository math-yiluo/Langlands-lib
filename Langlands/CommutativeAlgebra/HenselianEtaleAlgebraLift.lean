import Langlands.CommutativeAlgebra.HenselianSections
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Relative etale lifting into a prescribed Henselian local algebra -/

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands.CommutativeAlgebra.HenselianEtaleAlgebraLift

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {P A K E : Type u} [CommRing P] [CommRing A] [HenselianLocalRing A]
  [Algebra P A] [Field K] [Algebra A K] [Algebra P K] [IsScalarTower P A K]
  [CommRing E] [Algebra P E] [Algebra.Etale P E]

/-- A residue-valued point of an etale algebra over `P` lifts to a map into
any prescribed Henselian local `P`-algebra with that field quotient. -/
theorem exists_lift (hK : Function.Surjective (algebraMap A K)) (φ : E →ₐ[P] K) :
    ∃ σ : E →ₐ[P] A,
      ((Algebra.ofId A K).restrictScalars P).comp σ = φ := by
  let φA : A ⊗[P] E →ₐ[A] K := AlgHom.liftEquiv P A E K φ
  obtain ⟨τ, hτ⟩ := HenselianSections.exists_lift_of_etale hK φA
  refine ⟨(AlgHom.liftEquiv P A E A).symm τ, ?_⟩
  ext x
  change algebraMap A K (τ (1 ⊗ₜ[P] x)) = φ x
  have h := AlgHom.congr_fun hτ (1 ⊗ₜ[P] x)
  change algebraMap A K (τ (1 ⊗ₜ[P] x)) = φA (1 ⊗ₜ[P] x) at h
  exact h.trans (by simp only [φA, AlgHom.liftEquiv_tmul, one_smul])

/-- The lifted map extends to the local ring at the chosen residue point. -/
theorem exists_local_lift (hK : Function.Surjective (algebraMap A K)) (φ : E →ₐ[P] K) :
    letI : (RingHom.ker φ.toRingHom).IsPrime := RingHom.ker_isPrime _
    ∃ (σ : E →ₐ[P] A)
      (σloc : Localization.AtPrime (RingHom.ker φ.toRingHom) →ₐ[P] A),
      ((Algebra.ofId A K).restrictScalars P).comp σ = φ ∧
        σloc.comp (IsScalarTower.toAlgHom P E _) = σ := by
  have : (RingHom.ker φ.toRingHom).IsPrime := RingHom.ker_isPrime _
  obtain ⟨σ, hσ⟩ := exists_lift hK φ
  have hu : ∀ y : (RingHom.ker φ.toRingHom).primeCompl, IsUnit (σ y) := by
    intro y
    apply HenselianSections.isUnit_of_algebraMap_ne_zero hK
    have hy : φ y ≠ 0 := y.2
    exact (AlgHom.congr_fun hσ y).symm ▸ hy
  refine ⟨σ, IsLocalization.liftAlgHom hu, hσ, ?_⟩
  ext x
  exact IsLocalization.lift_eq hu x

end Langlands.CommutativeAlgebra.HenselianEtaleAlgebraLift
