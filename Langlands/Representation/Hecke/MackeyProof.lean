import Langlands.Representation.Hecke.MackeyStatements
import Langlands.Representation.Hecke.MackeyCurrying
import Langlands.Representation.Hecke.HomomorphismProof
import Langlands.Representation.Hecke.MackeyYoneda
import Langlands.Representation.Hecke.MackeyOpenness

/-! # Proof of Renard's two Mackey natural isomorphisms

Renard III.2.11 Theorem, printed pp.82–83 / PDF pp.88–89.
-/

noncomputable section

open CategoryTheory CategoryTheory.Prod Opposite

namespace Langlands.Hecke.Homomorphism

universe uG uH v

section Currying

variable (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The published smooth currying `smoothCurry`, as a currying datum for the actual
tensor and smooth Hom bifunctors. -/
def smoothCurrying :
    Mackey.Currying (smoothTensorBifunctor.{uG, v} G) (smoothHomBifunctor.{uG, v} G) where
  equiv E V X := smoothCurry E V.unop X
  equiv_naturality h j k f := by
    ext x
    apply Subtype.ext
    apply LinearMap.ext
    intro y
    rfl

end Currying

/-- Renard III.2.11: the Hom Mackey isomorphism for right Hecke induction, and the
tensor Mackey isomorphism for left Hecke induction under the pseudo-forgetful
comparison hypothesis, both natural in the two representations. -/
theorem mackeyIsomorphismStatements : MackeyIsomorphismStatements.{uG, uH, v} := by
  intro G _ _ _ _ _ _ _ H _ _ _ _ _ _ _ μG _ μH _ φ hφ
  obtain ⟨eG, eH, ⟨iso⟩, ⟨adjFI⟩, ⟨adjPpF⟩⟩ :=
    smoothInductionAdjunctionStatement.{uG, uH, v} G H μG μH φ hφ
  refine ⟨eG, eH, ⟨iso⟩, ⟨?_⟩, ?_⟩
  · exact Mackey.homMackeyIso (smoothCurrying.{uG, max uG v} G)
      (smoothCurrying.{uH, max uG v} H) (adjFI.ofNatIsoLeft iso.symm) (Iso.refl _)
  · rintro ⟨prem⟩
    have adj := adjPpF.ofNatIsoRight (prem ≪≫ iso.symm)
    exact ⟨Mackey.tensorMackeyIso (smoothCurrying.{uG, max uG v} G)
      (smoothCurrying.{uH, max uG v} H) adj
      (restrictionHomIso φ hφ (exists_openSubgroup_le_map_of_adjunction φ hφ adj))⟩

end Langlands.Hecke.Homomorphism
