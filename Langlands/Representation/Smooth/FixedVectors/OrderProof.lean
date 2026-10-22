import Langlands.Representation.Smooth.FixedVectors.OrderStatement

namespace Langlands

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [AddCommGroup V] [Module R V]

/-- A larger fixing subgroup has a smaller fixed-vector submodule. -/
theorem fixedVectors_antitone (ρ : Representation R G V) :
    Antitone (fixedVectors ρ) := by
  intro H K hHK v hv
  change ∀ h : H, ρ (h : G) v = v
  intro h
  exact hv ⟨h, hHK h.property⟩

theorem fixedVectorsAntitone :
    FixedVectorsAntitoneStatement (R := R) (G := G) (V := V) :=
  fixedVectors_antitone

end Langlands
