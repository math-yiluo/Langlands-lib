import Langlands.Representation.Smooth.SmoothPart.UniversalStatement

/-! # Unique factorization through the smooth part -/

namespace Langlands

universe uR uG uV uW

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
variable {ρ : Representation R G V} {σ : Representation R G W}

theorem smoothInclusion_comp_smoothLift (hσ : IsSmooth σ) (f : σ.IntertwiningMap ρ) :
    (smoothInclusion ρ).comp (smoothLift hσ f) = f := by
  ext v
  rfl

theorem smoothLift_unique (hσ : IsSmooth σ) (f : σ.IntertwiningMap ρ)
    (lift : σ.IntertwiningMap (smoothPart ρ)) (h : (smoothInclusion ρ).comp lift = f) :
    lift = smoothLift hσ f := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  exact congrArg (fun k : σ.IntertwiningMap ρ => k v) h

omit [IsTopologicalGroup G] in
theorem smoothPartUniversalProperty :
    SmoothPartUniversalProperty (R := R) (G := G) (V := V) (W := W) := by
  intro _ ρ σ hσ f
  exact ⟨smoothLift hσ f, smoothInclusion_comp_smoothLift hσ f,
    fun lift h => smoothLift_unique hσ f lift h⟩

end Langlands
