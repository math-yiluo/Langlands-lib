import Langlands.GroupScheme.IdentityJetDeterminantLine
import Langlands.AlgebraicGeometry.Picard.DeterminantDualFrames
import Langlands.AlgebraicGeometry.Picard.PositiveTensorPowerAmpleReflection

/-! # Actual jet determinants and the actual Lie determinant dual -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.IdentityJet

open Langlands.Scheme.Modules Algebra.SectionJet.Coordinates
open Langlands.AlgebraicGeometry.Picard

variable {S : Scheme.{u}} (G : GroupScheme S)
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    {σ ι : Type u} [Fintype σ] [DecidableEq σ]
    (U : ι → S.affineOpens) (hU : (⨆ i, (U i).1) = ⊤)
    (e : ∀ i, SheafOfModules.free (R := S.ringCatSheaf.over (U i).1) σ ≅
      G.cotangentAtIdentity.over (U i).1)

/-- The actual cotangent determinant is the dual of the actual Lie
determinant on a supplied fixed-index frame cover. -/
def cotangentLieDeterminantDualIso :
    finiteLocallyFreeDeterminant (G.cotangentAtIdentity_hasFiniteLocalBasis ‹Smooth G.X.hom›) ≅
      (finiteLocallyFreeDeterminant (G.lie_hasFiniteLocalBasis ‹Smooth G.X.hom›)).dual :=
  DeterminantFrames.finiteDeterminantDualIsoOfFrames e hU
    (G.cotangentAtIdentity_hasFiniteLocalBasis ‹Smooth G.X.hom›)
    (G.lie_hasFiniteLocalBasis ‹Smooth G.X.hom›)

/-- The existing actual positive-order jet determinant is a tensor power of
the existing actual Lie determinant dual. -/
def lieDeterminantPowerIsoOfAffineFrames (n : ℕ) :
    (determinant G n).obj ≅ tensorPow
      (finiteLocallyFreeDeterminant (G.lie_hasFiniteLocalBasis ‹Smooth G.X.hom›)).dual.obj
      (jetExponent σ n) :=
  chosenDeterminantPowerIsoOfAffineFrames G U hU e n ≪≫
    tensorPowIso ((LineBundle.forget S).mapIso
      (cotangentLieDeterminantDualIso G U hU e)) (jetExponent σ n)

include U hU e in
/-- Actual jet-determinant positivity implies positivity of the actual Lie
determinant dual on a supplied fixed-index affine cotangent frame cover. -/
theorem lieDeterminantDual_isAmple_of_jet (n : ℕ) (hn : 0 < n)
    (hJ : (determinant G n).IsAmple) :
    (finiteLocallyFreeDeterminant (G.lie_hasFiniteLocalBasis ‹Smooth G.X.hom›)).dual.IsAmple :=
  hJ.of_positive_tensorPower_iso (jetExponent_pos σ n hn)
    (lieDeterminantPowerIsoOfAffineFrames G U hU e n)

end Langlands.GroupScheme.IdentityJet
