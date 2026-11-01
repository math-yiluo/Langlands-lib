import Langlands.AlgebraicGeometry.Picard.SquareSecondProjectionFiniteSupportDetectionStatement
import Langlands.AlgebraicGeometry.Picard.SquareSecondFibre
import Langlands.AlgebraicGeometry.Picard.SquareSecondProjectionSupport
import Langlands.AlgebraicGeometry.Modules.FiniteClosedSupportCohomologyProof
import Langlands.AlgebraicGeometry.Modules.FiniteClosedSupportLerayProof
import Langlands.AlgebraicGeometry.Modules.HigherDirectImageVanishingAffineBaseChangeProof

/-! # Finite-support cohomology detection for the second abelian-square projection -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.Modules

/-- Finite exceptional fibre support and total cohomology vanishing force
vanishing on every fibre of the second abelian-square projection. -/
theorem algClosedFieldSquareSecondProjectionFiniteSupportDetection :
    AlgClosedFieldSquareSecondProjectionFiniteSupportDetectionStatement.{u} := by
  intro K _ _ A Q F
  dsimp only
  intro hF hQ hTotal x n
  let p2 := pullback.snd A.X.hom A.X.hom
  have hs := squareSecondProjectionSupport K A Q F hF hQ
  have hAll : ∀ q : ℕ, IsZero ((DerivedSections.higherDirectImage p2 q).obj Q.obj) := by
    intro q
    obtain ⟨e⟩ := finiteClosedSupportLeray _ _ (CommRingCat.of K) p2 A.X.hom Q.obj hs q
    have hz : IsZero
        ((DerivedSections.relativeCohomology (p2 ≫ A.X.hom) q).obj Q.obj) := by
      simpa only [p2, pullback.condition] using hTotal q
    exact ((finiteClosedSupportCohomology _ _ (hs q)).2.2 (CommRingCat.of K) A.X.hom).2.mp
      (hz.of_iso e.symm)
  have hFiber := higherDirectImageVanishingAffineBaseChange _ _ p2
    inferInstance inferInstance Q hAll (CommRingCat.of K) x.left n
  exact hFiber.of_iso
    (squareSecondFibreCohomologyIso A.X.hom x.left x.w Q.obj n).symm

end Langlands.AbelianScheme
