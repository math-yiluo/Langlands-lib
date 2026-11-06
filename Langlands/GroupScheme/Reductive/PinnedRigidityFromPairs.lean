import Langlands.GroupScheme.Reductive.PinnedRigidityReduction
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof

/-! # Pinned automorphism rigidity from split-pinned opposite-factor pairs -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Actual opposite-factor-pair existence, restricted to supplied split pinnings. -/
def SplitPinnedOppositeFactorPairsStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] (p : SplitPinning G),
    RelativeRoot.HasOppositeFactorPairs p.inclusion

namespace SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

/-- Actual pair existence for this pinning suffices for its automorphism rigidity. -/
theorem automorphism_eq_refl_of_pairExistence
    (hE : RelativeRoot.HasOppositeFactorPairs p.inclusion)
    (σ : G ≅ G) (hi : p.inclusion ≫ σ.hom = p.inclusion)
    (hf : ∀ a : p.base.support,
      Lie.targetMapLinear σ.hom k (p.pinning.rootVector a) = p.pinning.rootVector a) :
    σ = Iso.refl G := by
  exact p.automorphism_eq_refl_of_oppositeFactorPairs hE
    (maximalTorusCentralizer k G p.isConnectedReductive p.torus p.inclusion
      p.isMaximalTorus) σ hi hf

end SplitPinning

/-- The exact pinned-rigidity target has only split-pinned pair existence left
as a premise after applying the proved maximal-torus self-centralization theorem. -/
theorem pinnedAutomorphismRigidity_of_splitPinnedOppositeFactorPairs
    (h : SplitPinnedOppositeFactorPairsStatement.{u}) :
    PinnedAutomorphismRigidityStatement.{u} := by
  exact pinnedAutomorphismRigidity_of_prerequisites ⟨maximalTorusCentralizer, h⟩

end Langlands.GroupScheme
