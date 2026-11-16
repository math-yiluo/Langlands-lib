import Langlands.GroupScheme.CenterAutomorphisms

/-! # Existence of an automorphism moving the full centre -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- There is an actual group-scheme automorphism which does not fix the full
scheme-theoretic centre pointwise on all test schemes. -/
def HasCenterMovingAutomorphism (G : GroupScheme S) : Prop :=
  ∃ f : G ≅ G, ¬ AutomorphismFixesCenter f

namespace HasCenterMovingAutomorphism

/-- A centre-moving automorphism transports through an actual isomorphism. -/
theorem of_iso (h : HasCenterMovingAutomorphism G) (e : G ≅ H) :
    HasCenterMovingAutomorphism H := by
  obtain ⟨f, hf⟩ := h
  exact ⟨(e.symm.trans f).trans e,
    fun hfix => hf ((AutomorphismFixesCenter.conjugate_iff e f).mp hfix)⟩

/-- Existence of a centre-moving automorphism is independent of the actual
group-scheme model. -/
theorem iso_iff (e : G ≅ H) :
    HasCenterMovingAutomorphism G ↔ HasCenterMovingAutomorphism H :=
  ⟨fun h => h.of_iso e, fun h => h.of_iso e.symm⟩

end HasCenterMovingAutomorphism

end Langlands.GroupScheme
