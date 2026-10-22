import Langlands.Representation.Smooth.Transfer.StabilizerStatement

/-! Proof identifying smooth vectors by their open stabilizers. -/

namespace Langlands

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [AddCommGroup V] [Module R V]
variable {ρ : Representation R G V}

theorem isSmoothVector_iff_isOpen_stabilizer (v : V) :
    IsSmoothVector ρ v ↔ IsOpen (ρ.stabilizer v : Set G) := by
  constructor
  · rintro ⟨K, hK⟩
    apply Subgroup.isOpen_mono (H₁ := K.toSubgroup) (H₂ := ρ.stabilizer v)
    · intro g hg
      exact hK ⟨g, hg⟩
    · exact K.isOpen
  · intro hv
    refine ⟨⟨ρ.stabilizer v, hv⟩, ?_⟩
    intro g
    exact g.property

omit [IsTopologicalGroup G] in
theorem smoothVectorStabilizer :
    SmoothVectorStabilizerStatement (R := R) (G := G) (V := V) := by
  intro _ ρ v
  exact isSmoothVector_iff_isOpen_stabilizer v

end Langlands
