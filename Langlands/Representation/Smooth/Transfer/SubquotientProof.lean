import Langlands.Representation.Smooth.Transfer.SubquotientStatement

/-! Smoothness transfer along injective and surjective intertwiners. -/

namespace Langlands

universe uR uG uV uW

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW}
variable [CommRing R] [Group G] [TopologicalSpace G]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
variable {ρ : Representation R G V} {σ : Representation R G W}

omit [TopologicalSpace G] in
theorem mem_fixedVectors_iff (K : Subgroup G) (v : V) :
    v ∈ fixedVectors ρ K ↔ ∀ k : K, ρ (k : G) v = v :=
  Iff.rfl

theorem isSmoothVector_map (f : ρ.IntertwiningMap σ) {v : V}
    (hv : IsSmoothVector ρ v) : IsSmoothVector σ (f v) := by
  obtain ⟨K, hK⟩ := hv
  refine ⟨K, ?_⟩
  change ∀ k : K, σ (k : G) (f v) = f v
  intro k
  rw [← f.isIntertwining]
  exact congrArg f (hK k)

theorem isSmoothVector_of_injective (f : ρ.IntertwiningMap σ)
    (hf : Function.Injective f) {v : V} (hv : IsSmoothVector σ (f v)) :
    IsSmoothVector ρ v := by
  obtain ⟨K, hK⟩ := hv
  refine ⟨K, ?_⟩
  change ∀ k : K, ρ (k : G) v = v
  intro k
  apply hf
  rw [f.isIntertwining]
  exact hK k

theorem isSmooth_of_injective (f : ρ.IntertwiningMap σ)
    (hf : Function.Injective f) (hσ : IsSmooth σ) : IsSmooth ρ :=
  fun v => isSmoothVector_of_injective f hf (hσ (f v))

theorem isSmooth_of_surjective (f : ρ.IntertwiningMap σ)
    (hf : Function.Surjective f) (hρ : IsSmooth ρ) : IsSmooth σ := by
  intro w
  obtain ⟨v, rfl⟩ := hf w
  exact isSmoothVector_map f (hρ v)

theorem smoothSubquotient :
    SmoothSubquotientStatement (R := R) (G := G) (V := V) (W := W) := by
  intro ρ σ f
  exact ⟨isSmooth_of_injective f, isSmooth_of_surjective f⟩

end Langlands
