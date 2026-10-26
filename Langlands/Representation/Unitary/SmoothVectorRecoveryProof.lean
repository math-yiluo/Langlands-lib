import Langlands.Representation.Unitary.SmoothVectorRecoveryStatement

/-! # Admissible smooth-vector recovery in a dense realization -/

noncomputable section

namespace Langlands

universe uG uV uH

/-- The smooth vectors in a dense form-preserving realization of an admissible
representation are exactly the image of its algebraic carrier. -/
theorem admissibleSmoothVectorRecovery :
    AdmissibleSmoothVectorRecovery.{uG,uV,uH} := by
  intro G _ _ _ hcofinal V _ _ ρ hρ b H _ _ σ hσ j hj hform
  have hinvariant : ∀ (g : G) (x y : H),
      inner ℂ (σ g x) (σ g y) = inner ℂ x y := by
    intro g x y
    refine hj.induction_on₂
      (p := fun x y : H => inner ℂ (σ g x) (σ g y) = inner ℂ x y) ?_ ?_ x y
    · exact isClosed_eq
        (((hσ g).comp continuous_fst).inner ((hσ g).comp continuous_snd))
        (continuous_fst.inner continuous_snd)
    · intro v w
      rw [← j.isIntertwining, ← j.isIntertwining, hform, hform, b.invariant]
  intro w
  constructor
  · intro hw
    obtain ⟨K, hK⟩ := hw
    let ℓ : Module.Dual ℂ V := (innerₛₗ ℂ w).comp j.toLinearMap
    have hℓ : ℓ ∈ smoothVectors ρ.dual := by
      refine ⟨K, ?_⟩
      intro k
      apply LinearMap.ext
      intro v
      change inner ℂ w (j (ρ (k : G)⁻¹ v)) = inner ℂ w (j v)
      rw [j.isIntertwining]
      have h := hinvariant (k : G) w (σ (k : G)⁻¹ (j v))
      have hk : σ (k : G) w = w := hK k
      rw [hk, Representation.self_inv_apply] at h
      exact h.symm
    obtain ⟨v, hv⟩ := b.toSmoothDual_surjective hcofinal hρ ⟨ℓ, hℓ⟩
    refine ⟨v, hj.eq_of_inner_left ℂ fun x => ?_⟩
    have hx := congrArg (fun t : SmoothDual ρ => smoothDualPairing ρ t x) hv
    change b.inner v x = inner ℂ w (j x) at hx
    exact (hform v x).trans hx
  · rintro ⟨v, rfl⟩
    obtain ⟨K, hK⟩ := hρ.1 v
    refine ⟨K, ?_⟩
    intro k
    change σ (k : G) (j v) = j v
    rw [← j.isIntertwining]
    exact congrArg j (hK k)

end Langlands
