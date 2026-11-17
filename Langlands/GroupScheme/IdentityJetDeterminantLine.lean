import Langlands.GroupScheme.IdentityJetFrameDeterminant
import Langlands.GroupScheme.IdentityJetLocalBases
import Langlands.GroupScheme.Lie.FiniteLocalFrames
import Langlands.AlgebraicGeometry.Picard.CocycleLineBundlePower
import Langlands.AlgebraicGeometry.Picard.DeterminantFixedPresentation

/-! # Actual jet determinant lines from affine cotangent frames -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.IdentityJet

open Langlands.Scheme.Modules Algebra.SectionJet.Coordinates CoordinateWeights
open Langlands.AlgebraicGeometry.Picard

variable {S : Scheme.{u}} (G : GroupScheme S)
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    {σ ι : Type u} [Fintype σ] [DecidableEq σ]
    (U : ι → S.affineOpens) (hU : (⨆ i, (U i).1) = ⊤)
    (e : ∀ i, SheafOfModules.free (R := S.ringCatSheaf.over (U i).1) σ ≅
      G.cotangentAtIdentity.over (U i).1)

attribute [local instance] sectionAlgebra

variable
    (z : ∀ i, σ → Γ(G.X.left, G.X.hom ⁻¹ᵁ (U i)))
    (hz : ∀ i j, augmentation G (U i) (z i j) = 0)
    (hzb : ∀ i j, AugmentedAlgebra.classMap (augmentation G (U i)) (z i j) =
      cotangentFrameBasis G (U i) (e i) (U i) le_rfl j)

/-- The actual adapted jet frame family on the supplied affine cover. -/
def adaptedCoverFrames (n : ℕ) :
    ∀ i, SheafOfModules.free (R := S.ringCatSheaf.over (U i).1) (JetIndex σ n) ≅
      (module G n).over (U i).1 :=
  fun i => adaptedFrame G (U i) (e i) (z i) (hz i) (hzb i) n

theorem adaptedCoverFrames_cocycle (n : ℕ) :
    DeterminantFrames.cocycle (adaptedCoverFrames G U e z hz hzb n) =
      DeterminantFrames.cocycle e ^ jetExponent σ n := by
  funext i j
  apply Units.ext
  have hh := adaptedOverlapMatrix_det G (U i) (U j) (e i) (e j)
    (z i) (hz i) (hzb i) (z j) (hz j) (hzb j) n
      ((U i).1 ⊓ (U j).1) inf_le_left inf_le_right
  simp only [DeterminantFrames.cocycle, DeterminantFrames.unit_val,
    DeterminantFrames.matrix, DeterminantFrames.basis, adaptedCoverFrames,
    adaptedOverlapMatrix, cotangentOverlapMatrix, Pi.pow_apply,
    Units.val_pow_eq_pow_val] at hh ⊢
  convert! hh using 1
  · congr 1
  · congr 2

/-- On a supplied affine cotangent frame cover with fixed finite index, the
existing actual jet determinant is the corresponding tensor power of the
existing actual cotangent determinant. -/
def determinantPowerIsoOfAffineFrames (n : ℕ) :
    (determinant G n).obj ≅
      tensorPow
        (finiteLocallyFreeDeterminant
          (G.cotangentAtIdentity_hasFiniteLocalBasis ‹Smooth G.X.hom›)).obj
        (jetExponent σ n) := by
  let EJ := DeterminantFrames.finiteDeterminantPresentationIso
    (adaptedCoverFrames G U e z hz hzb n) hU (hasFiniteLocalBasis G n)
  let EC := DeterminantFrames.finiteDeterminantPresentationIso e hU
    (G.cotangentAtIdentity_hasFiniteLocalBasis ‹Smooth G.X.hom›)
  exact (LineBundle.forget S).mapIso EJ.symm ≪≫
    eqToIso (congrArg CocycleGluing.glued (adaptedCoverFrames_cocycle G U e z hz hzb n)) ≪≫
    (CocycleGluing.powerIso (DeterminantFrames.cocycle e)
      (DeterminantFrames.isCocycle e) hU (jetExponent σ n)).symm ≪≫
    tensorPowIso ((LineBundle.forget S).mapIso EC) (jetExponent σ n)

/-- Choosing augmentation lifts removes them from the inputs to the actual
determinant-power comparison on a supplied affine frame cover. -/
def chosenDeterminantPowerIsoOfAffineFrames (n : ℕ) :
    (determinant G n).obj ≅
      tensorPow
        (finiteLocallyFreeDeterminant
          (G.cotangentAtIdentity_hasFiniteLocalBasis ‹Smooth G.X.hom›)).obj
        (jetExponent σ n) := by
  choose z hz hzb using fun i =>
    exists_basis_lifts (ε := augmentation G (U i))
      (cotangentFrameBasis G (U i) (e i) (U i) le_rfl)
  exact determinantPowerIsoOfAffineFrames G U hU e z hz hzb n

end Langlands.GroupScheme.IdentityJet
