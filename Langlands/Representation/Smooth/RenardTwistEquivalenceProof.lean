import Langlands.Representation.Smooth.RenardCoinvariantTensorStatements
import Mathlib.CategoryTheory.Adjunction.Basic

noncomputable section

open CategoryTheory

namespace Langlands.Renard.Smooth

universe r u v

namespace CharacterTwist

variable {R : Type r} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
variable (ω : G →* Rˣ) (hω : IsOpen (ω.ker : Set G))
  (hω' : IsOpen ((ω⁻¹).ker : Set G))

/-- Inverse twisting cancels twisting, naturally on the original carrier. -/
def cancel : SmoothRep.twistFunctor.{r, u, v} ω hω ⋙ SmoothRep.twistFunctor ω⁻¹ hω' ≅
    𝟭 (SmoothRep.{r, u, v} R G) :=
  NatIso.ofComponents
    (fun A => SmoothRep.mkIso (equivOfRepresentationEq (twist_inv_twist ω A.representation)))
    (by intro A B f; ext x; rfl)

/-- Twisting cancels inverse twisting, naturally on the original carrier. -/
def cancel' : SmoothRep.twistFunctor.{r, u, v} ω⁻¹ hω' ⋙ SmoothRep.twistFunctor ω hω ≅
    𝟭 (SmoothRep.{r, u, v} R G) :=
  NatIso.ofComponents
    (fun A => SmoothRep.mkIso (equivOfRepresentationEq (twist_twist_inv ω A.representation)))
    (by intro A B f; ext x; rfl)

/-- The two character twists give an equivalence of the full smooth category. -/
def equivalence : SmoothRep.{r, u, v} R G ≌ SmoothRep.{r, u, v} R G :=
  CategoryTheory.Equivalence.mk (SmoothRep.twistFunctor ω hω)
    (SmoothRep.twistFunctor ω⁻¹ hω') (cancel ω hω hω').symm (cancel' ω hω hω')

end CharacterTwist

/-- Renard III.1.15, Remark 3, including both adjunctions. -/
theorem twistEquivalence : TwistEquivalenceStatement.{u, v} := by
  intro G _ _ _ _ _ ω hω hω'
  exact ⟨⟨CharacterTwist.cancel ω hω hω'⟩, ⟨CharacterTwist.cancel' ω hω hω'⟩,
    ⟨(CharacterTwist.equivalence ω hω hω').symm.toAdjunction⟩,
    ⟨(CharacterTwist.equivalence ω hω hω').toAdjunction⟩⟩

end Langlands.Renard.Smooth
