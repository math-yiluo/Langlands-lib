import Mathlib.Algebra.Group.Subgroup.Ker

/-! # Group-theoretic kernel transport for the Kottwitz argument -/

namespace Langlands.Geometry.Building.Kottwitz

variable {H G A B : Type*} [Group H] [Group G] [Group A] [Group B]

/-- A surjective square maps kernels onto kernels when the left map lifts the
kernel of the target map from the kernel of the point map. -/
theorem map_kernel_eq_of_kernel_lift
    (p : H →* G) (κH : H →* A) (κG : G →* B) (q : A →* B)
    (hp : Function.Surjective p)
    (hsquare : ∀ h, κG (p h) = q (κH h))
    (hlift : ∀ a ∈ q.ker, ∃ h ∈ p.ker, κH h = a) :
    κH.ker.map p = κG.ker := by
  apply le_antisymm
  · rintro _ ⟨h, hh, rfl⟩
    change κG (p h) = 1
    rw [hsquare, (show κH h = 1 from hh), map_one]
  · intro g hg
    obtain ⟨h, rfl⟩ := hp g
    have ha : κH h ∈ q.ker := by
      change q (κH h) = 1
      rw [← hsquare]
      exact hg
    obtain ⟨z, hz, hκz⟩ := hlift (κH h) ha
    refine ⟨h * z⁻¹, ?_, ?_⟩
    · change κH (h * z⁻¹) = 1
      simp [hκz]
    · simp [show p z = 1 from hz]

/-- A subgroup is the inverse image of its image if it contains the point-map kernel. -/
theorem comap_eq_of_map_eq_of_kernel_le
    (p : H →* G) (S : Subgroup H) (T : Subgroup G)
    (himage : S.map p = T) (hker : p.ker ≤ S) :
    T.comap p = S := by
  subst T
  apply le_antisymm
  · intro h hh
    obtain ⟨s, hs, heq⟩ := hh
    have hdiff : h * s⁻¹ ∈ p.ker := by
      change p (h * s⁻¹) = 1
      simp [heq]
    have := S.mul_mem (hker hdiff) hs
    simpa using this
  · intro h hh
    exact ⟨h, hh, rfl⟩

end Langlands.Geometry.Building.Kottwitz
