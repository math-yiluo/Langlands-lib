import Langlands.GroupScheme.IntegralModel.ScaledVectorPoints

/-! # Scalar transitions determined by exact vector lattices -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

variable (R K : Type u) [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] (n : ℕ)

/-- For a positive-dimensional vector group, inclusion of the actual integral
point lattices is equivalent to an integral scalar transition coefficient. -/
theorem scaledVector_integralPoints_le_iff (hn : 0 < n) (s t : Kˣ) :
    (scaledVector R K n s).integralPoints ≤ (scaledVector R K n t).integralPoints ↔
      ∃ c : R, algebraMap R K c * (t : K) = s := by
  constructor
  · intro h
    let g := (VectorGroup.sectionCoordinates (CommRingCat.of K) n).symm
      (Multiplicative.ofAdd (fun _ => (s : K)))
    have hg : g ∈ (scaledVector R K n s).integralPoints := by
      apply (scaledVector_mem_integralPoints R K n s g).mpr
      refine ⟨fun _ => 1, ?_⟩
      intro j
      simp [g]
    obtain ⟨v, hv⟩ := (scaledVector_mem_integralPoints R K n t g).mp (h hg)
    refine ⟨v ⟨0, hn⟩, ?_⟩
    have he := hv ⟨0, hn⟩
    simp only [g, MulEquiv.apply_symm_apply] at he
    rw [mul_comm]
    exact he.symm
  · rintro ⟨c, hc⟩ g hg
    obtain ⟨v, hv⟩ := (scaledVector_mem_integralPoints R K n s g).mp hg
    apply (scaledVector_mem_integralPoints R K n t g).mpr
    refine ⟨fun j => c * v j, ?_⟩
    intro j
    rw [hv j, map_mul, ← mul_assoc, mul_comm (t : K) (algebraMap R K c), hc]

/-- Inclusion of positive-dimensional scaled vector lattices supplies an
actual model homomorphism extending the generic identity. -/
def scaledVectorTransitionOfIntegralPointsLE (hn : 0 < n) (s t : Kˣ)
    (h : (scaledVector R K n s).integralPoints ≤
      (scaledVector R K n t).integralPoints) :
    (scaledVector R K n s).Hom (scaledVector R K n t) (𝟙 _) :=
  let hc := (scaledVector_integralPoints_le_iff R K n hn s t).mp h
  scaledVectorTransition s t hc.choose hc.choose_spec

variable [IsLocalRing R]

/-- Every identity extension between nested positive-dimensional principal
vector lattices has a smooth connected unipotent actual special-fibre kernel. -/
theorem scaledVector_kernel_properties_of_integralPoints_le
    (hn : 0 < n) (s t : Kˣ)
    (h : (scaledVector R K n s).integralPoints ≤
      (scaledVector R K n t).integralPoints)
    (φ : (scaledVector R K n s).Hom (scaledVector R K n t) (𝟙 _)) :
    Smooth (kernel φ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel φ.specialFibreMap).X.left ∧
        IsUnipotent (kernel φ.specialFibreMap) := by
  obtain ⟨c, hc⟩ := (scaledVector_integralPoints_le_iff R K n hn s t).mp h
  exact scaledVector_kernel_properties s t c hc φ

end Langlands.GroupScheme.IntegralModel
