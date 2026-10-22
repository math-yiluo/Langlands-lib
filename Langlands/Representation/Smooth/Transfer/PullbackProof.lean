import Langlands.Representation.Smooth.Transfer.PullbackStatement

/-! Smoothness under continuous pullback. -/

namespace Langlands

universe uR uG uV uH

variable {R : Type uR} {G : Type uG} {V : Type uV} {H : Type uH}
variable [CommRing R] [Group G] [TopologicalSpace G]
variable [AddCommGroup V] [Module R V] [Group H] [TopologicalSpace H]
variable {ρ : Representation R G V}

theorem isSmoothVector_comp (φ : H →* G) (hφ : Continuous φ)
    {v : V} (hv : IsSmoothVector ρ v) : IsSmoothVector (ρ.comp φ) v := by
  obtain ⟨K, hK⟩ := hv
  refine ⟨K.comap φ hφ, ?_⟩
  change ∀ h : K.comap φ hφ, ρ (φ (h : H)) v = v
  intro h
  exact hK ⟨φ (h : H), h.property⟩

theorem isSmooth_comp (φ : H →* G) (hφ : Continuous φ)
    (hρ : IsSmooth ρ) : IsSmooth (ρ.comp φ) :=
  fun v => isSmoothVector_comp φ hφ (hρ v)

theorem smoothPullback :
    SmoothPullbackStatement (R := R) (G := G) (V := V) (H := H) := by
  intro ρ φ hφ hρ
  exact isSmooth_comp φ hφ hρ

end Langlands
