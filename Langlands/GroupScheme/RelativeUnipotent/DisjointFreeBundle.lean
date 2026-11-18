import Langlands.AlgebraicGeometry.Modules.DirectImageAffineCriterion
import Langlands.GroupScheme.RelativeUnipotent.FreeVectorBundle
import Langlands.AlgebraicGeometry.Picard.CoproductChartLineBundle
import Langlands.AlgebraicGeometry.Picard.FiniteLocallyFreeDeterminant
import Langlands.AlgebraicGeometry.Modules.FixedRankLocalBases

/-! # Actual finite free bundles on disjoint open covers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Scheme.Modules Langlands.AlgebraicGeometry.Picard

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeUnipotent.DisjointFreeBundle

variable {X : Scheme.{u}} (𝒰 : X.OpenCover.{u})
  (h : DisjointCoverGluing.IsDisjoint 𝒰) (n : 𝒰.I₀ → ℕ)

/-- The actual module obtained by gluing the prescribed finite free pieces. -/
def module : X.Modules :=
  OpenCoverModuleGluing.glued 𝒰 (fun i => freeBundle (𝒰.X i) (n i))
    (DisjointCoverGluing.transition h _)

/-- Pullback recovers the original free sheaf on every component. -/
def pieceIso (i : 𝒰.I₀) :
    (Scheme.Modules.pullback (𝒰.f i)).obj (module 𝒰 h n) ≅
      freeBundle (𝒰.X i) (n i) :=
  OpenCoverModuleGluing.pieceIso 𝒰 (fun i => freeBundle (𝒰.X i) (n i))
    (DisjointCoverGluing.transition h _) (DisjointCoverGluing.cocycle h _) i

/-- The actual finite local frames retain each component's own finite rank. -/
def frames : FiniteLocalFrames (module 𝒰 h n) where
  I := 𝒰.I₀
  opens i := (𝒰.f i).opensRange
  covers := 𝒰.iSup_opensRange
  rank := n
  frame i := freeOverIsoOfRestrict (module 𝒰 h n) (𝒰.f i).opensRange
    (ULift.{u} (Fin (n i)))
    (Langlands.AlgebraicGeometry.Modules.DerivedSections.freeChartOnOpensRange (module 𝒰 h n) (𝒰.f i) _
      ((Scheme.Modules.restrictFunctorIsoPullback (𝒰.f i)).app _ ≪≫
        pieceIso 𝒰 h n i))

/-- Gluing finitely generated free pieces on a disjoint cover gives an actual
finite locally free sheaf, without a common-rank assumption. -/
theorem isFiniteLocallyFree : IsFiniteLocallyFree (module 𝒰 h n) :=
  (frames 𝒰 h n).hasFiniteLocalBasis

end Langlands.GroupScheme.RelativeUnipotent.DisjointFreeBundle
