import Langlands.GroupScheme.IdentityJetSeparatedLocalBases

/-! # Geometry of the actual identity-jet projection -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.IdentityJet

/-- Finiteness, flatness and local finite presentation of the projection of
an actual identity jet in a smooth separated group. -/
theorem projection_geometry {S : Scheme.{u}} (G : GroupScheme S)
    [IsSeparated G.X.hom] [Smooth G.X.hom] (n : ℕ) :
    IsFinite (projection G n) ∧ Flat (projection G n) ∧ LocallyOfFinitePresentation (projection G n) :=
  ⟨finite_projection G n, flat_projection G n, locallyOfFinitePresentation_projection G n⟩

/-- Finite-flat geometry and finite local module bases of all actual identity
jets of every smooth separated group. -/
def SeparatedIdentityJetLocalBasesStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S) [IsSeparated G.X.hom] [Smooth G.X.hom] (n : ℕ),
    IsFinite (projection G n) ∧ Flat (projection G n) ∧
      LocallyOfFinitePresentation (projection G n) ∧
      Langlands.Scheme.Modules.HasFiniteLocalBasis (module G n)

theorem separatedIdentityJetLocalBases : SeparatedIdentityJetLocalBasesStatement.{u} := by
  intro S G _ _ n
  obtain ⟨hfinite, hflat, hfp⟩ := projection_geometry G n
  exact ⟨hfinite, hflat, hfp, hasFiniteLocalBasis_of_separated G n⟩

end Langlands.GroupScheme.IdentityJet
