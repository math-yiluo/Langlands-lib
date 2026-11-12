import Langlands.Representation.Unitary.InvariantSesquilinearScalarStatement
import Langlands.Representation.Unitary.HermitianDual
import Langlands.Representation.Unitary.HermitianAdmissibleProof
import Langlands.Representation.Smooth.Schur.Proof

/-! # Scalar comparison with a positive invariant form -/

noncomputable section

namespace Langlands

open Renard.CompactRepresentation.HermitianProof

universe uG uV

/-- Comparing the arbitrary-form map into the smooth dual with the positive
form identification reduces the assertion to admissible Schur's lemma. -/
theorem invariantSesquilinearScalar :
    InvariantSesquilinearScalarStatement.{uG, uV} := by
  intro G _ _ _ hcof V _ _ ρ ha hi b B hB hinv
  let e := b.smoothDualEquiv hcof ha
  let F := pairingToSmoothDual ρ B hinv ha.1
  let A : V →ₗ[ℂ] V := e.symm.toLinearMap.comp F
  have hAe (v : V) : e (A v) = F v := e.apply_symm_apply (F v)
  have hAact (g : G) (v : V) : A (ρ g v) = ρ g (A v) := by
    apply e.injective
    rw [hAe]
    change pairingToSmoothDual ρ B hinv ha.1 (ρ g v) =
      b.toSmoothDual ha.1 (ρ g (A v))
    rw [pairingToSmoothDual_action, b.toSmoothDual_apply_action]
    exact congrArg (smoothContragredient ρ g) (hAe v).symm
  let f : ρ.IntertwiningMap ρ :=
    A.intertwiningMap_of_isIntertwiningMap ρ ρ hAact
  obtain ⟨z, hz, _⟩ := admissibleSchur_scalarEndomorphism ρ ha hi f
  have hscalar (v w : V) : B v w = starRingEnd ℂ z * b.inner v w := by
    have hv : A v = z • v :=
      congrArg (fun f : ρ.IntertwiningMap ρ => f v) hz
    calc
      B v w = b.inner (A v) w :=
        (congrArg (fun ℓ : SmoothDual ρ => ℓ.val w) (hAe v)).symm
      _ = starRingEnd ℂ z * b.inner v w := by rw [hv, b.smul_left]
  refine ⟨starRingEnd ℂ z, ?_, hscalar⟩
  intro hz0
  apply hB
  ext v w
  simp only [hscalar, hz0, zero_mul, LinearMap.zero_apply]

end Langlands
