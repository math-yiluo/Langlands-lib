import Langlands.GroupScheme.IdentityJetRankReduction
import Langlands.GroupScheme.IdentityJetOpenBaseChange
import Langlands.AlgebraicGeometry.Picard.AffineBaseLineTwistAmple

/-! # Actual positive-order identity jets give Lie determinant-dual ampleness -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.IdentityJet

open Langlands.AlgebraicGeometry.Picard
open Langlands.Scheme.Modules

variable {S T : Scheme.{u}} (G : GroupScheme S)
    [IsAffineHom G.X.hom] [Smooth G.X.hom]

local instance ampleTransfer_baseGroup_affine (b : T ⟶ S) :
    IsAffineHom ((baseChange b).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  exact MorphismProperty.pullback_snd _ _ ‹IsAffineHom G.X.hom›

local instance ampleTransfer_baseGroup_smooth (b : T ⟶ S) :
    Smooth ((baseChange b).obj G).X.hom := by
  change Smooth (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

/-- Actual chosen jet determinants commute with open base change, by the
actual jet-module isomorphism and determinant functoriality. -/
def openDeterminantBaseChangeIso (b : T ⟶ S) [IsOpenImmersion b] (n : ℕ) :
    (LineBundle.pullback b).obj (determinant G n) ≅
      determinant ((baseChange b).obj G) n :=
  finiteLocallyFreeDeterminantPullbackIso (hasFiniteLocalBasis G n) b ≪≫
    finiteLocallyFreeDeterminantIso ((hasFiniteLocalBasis G n).pullback b)
      (hasFiniteLocalBasis ((baseChange b).obj G) n) (openBaseChangeIso G b n)

variable [CompactSpace S] [QuasiSeparatedSpace S]

/-- An ample actual positive-order jet determinant implies ampleness of the
actual smooth Lie determinant dual, without any rank or base-change premise. -/
theorem lieDeterminantDual_isAmple_of_positiveJet (n : ℕ) (hn : 0 < n)
    (hJ : (determinant G n).IsAmple) :
    (smoothLieDeterminant G ‹Smooth G.X.hom›).dual.IsAmple :=
  lieDeterminantDual_isAmple_of_jet_rankBaseChange G n hn hJ
    (fun k => ⟨openBaseChangeIso G ((cotangentRankFrames G).rankOpen k).ι n⟩)

/-- An ample actual line identified with a positive-order jet determinant
twisted by an actual affine-base line also implies Lie determinant-dual ampleness. -/
theorem lieDeterminantDual_isAmple_of_positiveJet_twist
    {B : Scheme.{u}} [IsAffine B] (p : S ⟶ B)
    (n : ℕ) (hn : 0 < n) (N : LineBundle B) (M : LineBundle S)
    (e : M.obj ≅ tensorObj (determinant G n).obj
      ((Scheme.Modules.pullback p).obj N.obj)) (hM : M.IsAmple) :
    (smoothLieDeterminant G ‹Smooth G.X.hom›).dual.IsAmple :=
  lieDeterminantDual_isAmple_of_positiveJet G n hn
    ((isAmple_iff_of_affine_base_twist p (determinant G n) M N e).mp hM)

end Langlands.GroupScheme.IdentityJet
