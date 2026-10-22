import Langlands.Representation.Twist.SmoothStatement

namespace Langlands

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [TopologicalSpace G]
variable [AddCommGroup V] [Module R V]

theorem isSmoothVector_twist_iff (chi : G →* Rˣ) (rho : Representation R G V)
    (hchi : IsOpen (chi.ker : Set G)) (v : V) :
    IsSmoothVector (twist chi rho) v ↔ IsSmoothVector rho v := by
  let L : OpenSubgroup G := ⟨chi.ker, hchi⟩
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨K ⊓ L, ?_⟩
    intro g
    have hg : chi (g : G) = 1 := g.property.2
    have h := hK ⟨(g : G), g.property.1⟩
    change (chi (g : G) : R) • rho (g : G) v = v at h
    change rho (g : G) v = v
    simpa [hg] using h
  · rintro ⟨K, hK⟩
    refine ⟨K ⊓ L, ?_⟩
    intro g
    have hg : chi (g : G) = 1 := g.property.2
    have h := hK ⟨(g : G), g.property.1⟩
    change rho (g : G) v = v at h
    change (chi (g : G) : R) • rho (g : G) v = v
    simpa [hg] using h

theorem isSmooth_twist_iff (chi : G →* Rˣ) (rho : Representation R G V)
    (hchi : IsOpen (chi.ker : Set G)) :
    IsSmooth (twist chi rho) ↔ IsSmooth rho := by
  constructor
  · intro h v
    exact (isSmoothVector_twist_iff chi rho hchi v).mp (h v)
  · intro h v
    exact (isSmoothVector_twist_iff chi rho hchi v).mpr (h v)

theorem twistSmoothCompatibility :
    TwistSmoothCompatibility (R := R) (G := G) (V := V) := by
  intro chi rho hchi
  exact ⟨isSmoothVector_twist_iff chi rho hchi, isSmooth_twist_iff chi rho hchi⟩

end Langlands
