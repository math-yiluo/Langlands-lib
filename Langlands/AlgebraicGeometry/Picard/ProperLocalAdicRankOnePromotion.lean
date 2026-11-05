import Langlands.Algebra.AdicRankOneReflection
import Langlands.AlgebraicGeometry.Modules.RankOneStalkReflection
import Langlands.AlgebraicGeometry.ProperLocalClosedFibreCover
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Promoting adic stalk frames to an actual line bundle -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

variable {X : Scheme.{u}}

/-- Rank-one frames of every adic quotient give a frame of the actual stalk. -/
def stalkRankOneEquivOfAdicQuotients (M : X.Modules) [M.IsFinitePresentation]
    (x : X) [IsNoetherianRing (X.presheaf.stalk x)]
    (J : Ideal (X.presheaf.stalk x)) (hJ : J ≠ ⊤)
    (h : ∀ n : ℕ, Nonempty
      ((stalk M x ⧸ (J ^ (n + 1) •
        (⊤ : Submodule (X.presheaf.stalk x) (stalk M x)))) ≃ₗ[X.presheaf.stalk x]
        ((X.presheaf.stalk x) ⧸ J ^ (n + 1)))) :
    stalk M x ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x := by
  have : Module.FinitePresentation (X.presheaf.stalk x) (stalk M x) :=
    finitePresentation_stalk M x
  exact Langlands.Algebra.AdicRankOne.equivOfAdicQuotients
    (X.presheaf.stalk x) (stalk M x) J hJ h

end Langlands.AlgebraicGeometry.Modules

namespace Langlands.AlgebraicGeometry.Picard

variable {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) [UniversallyClosed f]

/-- Frames of all actual stalks on the closed fibre make a finitely presented
module locally free of rank one everywhere. -/
lemma isLocallyFreeRankOne_of_closedFibre_stalkEquivs
    (M : X.Modules) [M.IsFinitePresentation]
    (h : ∀ x : X, f x = IsLocalRing.closedPoint R →
      Nonempty (Modules.stalk M x ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x)) :
    IsLocallyFreeRankOne M := by
  apply (rankOneLocus_eq_top_iff M).mp
  apply open_eq_top_of_contains_closedFibre f
  intro x hx
  exact Modules.mem_rankOneLocus_of_stalkEquiv M x (h x hx).some

/-- The line bundle with original underlying module, constructed from rank-one
adic quotient stalks on the closed fibre. -/
def lineBundleOfClosedFibreAdicStalkQuotients [IsLocallyNoetherian X]
    (M : X.Modules) [M.IsFinitePresentation]
    (h : ∀ x : X, f x = IsLocalRing.closedPoint R →
      ∃ J : Ideal (X.presheaf.stalk x), J ≠ ⊤ ∧
        ∀ n : ℕ, Nonempty
          ((Modules.stalk M x ⧸ (J ^ (n + 1) •
            (⊤ : Submodule (X.presheaf.stalk x) (Modules.stalk M x)))) ≃ₗ[X.presheaf.stalk x]
            ((X.presheaf.stalk x) ⧸ J ^ (n + 1)))) :
    LineBundle X :=
  ⟨M, isLocallyFreeRankOne_of_closedFibre_stalkEquivs f M (by
    intro x hx
    obtain ⟨J, hJ, hquot⟩ := h x hx
    exact ⟨Modules.stalkRankOneEquivOfAdicQuotients M x J hJ hquot⟩)⟩

end Langlands.AlgebraicGeometry.Picard
