import Langlands.AlgebraicGeometry.Picard.Ample
import Langlands.AlgebraicGeometry.ProjectiveSpace.Charts
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_projPresentation_toProj_eq_and_locallyTrivial
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Projective embeddings by sections from properness and ampleness -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- The existence of an invertible module presented by a closed projective
immersion is equivalent to the Library's actual H-projectivity predicate. -/
theorem exists_closedImmersionBySections_iff_isHProjective
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) :
    (∃ M : X.Modules, Scheme.Modules.IsInvertible M ∧
      Scheme.Modules.ClosedImmersionBySections M f) ↔ IsHProjective f := by
  constructor
  · rintro ⟨M, _, n, p, hp⟩
    exact ⟨n, p.toProj, hp, p.toProj_π⟩
  · rintro ⟨n, i, hi, hcomp⟩
    obtain ⟨M, p, hp, hloc⟩ :=
      _root_.AlgebraicGeometry.ProjSpace.exists_projPresentation_toProj_eq_and_locallyTrivial
        (A := R) (n := n) i
    refine ⟨M, ⟨hloc⟩, ?_⟩
    have hf : i ≫ _root_.AlgebraicGeometry.ProjSpace.π R n = f := hcomp
    rw [← hf]
    exact ⟨n, p, by rw [hp]; exact hi⟩

/-- A proper scheme over an affine noetherian base with an ample line bundle
admits the actual projective presentation required by the Hilbert construction. -/
def ProperAmpleClosedImmersionBySectionsStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of R)),
    IsProper f → (∃ L : LineBundle X, L.IsAmple) →
      ∃ M : X.Modules, Scheme.Modules.IsInvertible M ∧
        Scheme.Modules.ClosedImmersionBySections M f

end Langlands.AlgebraicGeometry.Picard
