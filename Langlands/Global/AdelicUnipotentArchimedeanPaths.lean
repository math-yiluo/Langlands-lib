import Langlands.Global.InfiniteAdelicGroupManifold
import Langlands.Global.ArchimedeanFundamentalSet
import Langlands.GroupScheme.AffinePointFiniteCoordinates
import Langlands.GroupScheme.Unipotent.PerfectFieldSplitProof
import Langlands.GroupScheme.Unipotent.SplitAffineSpaceProof

/-! # Smooth paths in the archimedean unipotent group -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory NumberField Set
open scoped Classical CategoryTheory.MonObj Manifold ContDiff

namespace Langlands.Global.InfiniteAdelicGroupPoints

open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

variable {F : Type u} [Field F] [NumberField F]
  {U : GroupScheme (Spec (CommRingCat.of F))} [IsAffine U.X.left]
  {d : ℕ} (hU : SmoothOfRelativeDimension d U.X.hom)

local notation "U∞" => InfiniteAdelicGroupPoints F U
local notation "E∞" => mixedEmbedding.mixedSpace F
local notation "I∞" => 𝓘(ℝ, smoothModel F d)

/-- The actual archimedean points of a smooth connected affine unipotent group admit a
jointly smooth family of paths from the identity to each point. -/
def AdelicUnipotentArchimedeanPathsStatement : Prop :=
  ConnectedSpace U.X.left → IsUnipotent U →
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F U hU
  ∃ p : U∞ × ℝ → U∞, ContMDiff (I∞.prod 𝓘(ℝ, ℝ)) I∞ ∞ p ∧
    (∀ v : U∞, p (v, 0) = 1) ∧ (∀ v : U∞, p (v, 1) = v)

theorem adelicUnipotentArchimedeanPaths : AdelicUnipotentArchimedeanPathsStatement hU := by
  intro hconn hu
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F U hU
  let : IsAffineHom U.X.hom := isAffineHom_of_isAffine _
  let : Smooth U.X.hom := hU.smooth
  obtain ⟨n, hn⟩ := perfectFieldUnipotentSplit F U hconn hu
  obtain ⟨e⟩ := splitUnipotentAffineSpaceStatement F n U inferInstance hn
  let J := ULift.{u} (Fin n)
  let R := CommRingCat.of F
  let A := CommAlgCat.of F (InfiniteAdeleRing F)
  let Y := ringTest F (MvPolynomial J F)
  let eSpec : Y ≅ Over.mk (𝔸(J; Spec R) ↘ Spec R) :=
    Over.isoMk (AffineSpace.SpecIso J R).symm (AffineSpace.SpecIso_inv_over R)
  let S : AffineCoordinateRing F U.X ≃ₐ[F] MvPolynomial J F :=
    (affineCoordinateAlgEquiv F (e ≪≫ eSpec.symm)).symm.trans (spectrumCoordinateAlgEquiv F _)
  let c := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let Q : U∞ ≃ₜ (J → E∞) := ((U.affinePointsAlgebraHomeomorph A).trans
    ((AlgPoint.congr S).trans (AlgPoint.polynomialPointHomeomorph J))).trans
      (Homeomorph.piCongrRight (fun _ => infiniteAdeleHomeomorph F))
  have hQ (v : U∞) (i : J) : Q v i = c (U.affinePointEvaluation A v (S.symm (MvPolynomial.X i))) := by
    change c ((U.affinePointsAlgebraHomeomorph A v) _) = _
    rw [U.affinePointsAlgebraHomeomorph_apply]
    rfl
  have hQinv (v : J → E∞) (a : AffineCoordinateRing F U.X) :
      U.affinePointEvaluation A (Q.symm v) a =
        MvPolynomial.aeval (fun i => c.symm (v i)) (S a) := by
    rw [← U.affinePointsAlgebraHomeomorph_apply A]
    simp only [Q, Homeomorph.symm_trans_apply]
    rw [Homeomorph.apply_symm_apply]
    rfl
  have hp : ContMDiff 𝓘(ℝ, J → E∞) I∞ ∞ Q.symm := by
    apply (contMDiff_iff_coordinateSmooth F U 𝓘(ℝ, J → E∞) hU _).mpr
    intro a
    change ContMDiff 𝓘(ℝ, J → E∞) 𝓘(ℝ, E∞) ∞
      (fun v : J → E∞ => c (U.affinePointEvaluation A (Q.symm v) a))
    simp only [hQinv]
    generalize S a = b
    induction b using MvPolynomial.induction_on with
    | C a =>
        simp only [MvPolynomial.aeval_C]
        exact contMDiff_const
    | add b e hb he =>
        simp only [map_add]
        exact hb.add he
    | mul_X b i hb =>
        simp only [map_mul, MvPolynomial.aeval_X, c.apply_symm_apply]
        have hi : ContMDiff 𝓘(ℝ, J → E∞) 𝓘(ℝ, E∞) ∞ (fun v : J → E∞ => v i) :=
          contMDiff_pi_space.mp contMDiff_id i
        exact (hb.contDiff.mul hi.contDiff).contMDiff
  have hq (i : J) : ContMDiff I∞ 𝓘(ℝ, E∞) ∞ (fun v : U∞ => Q v i) := by
    simp only [hQ]
    exact contMDiff_mixedEvaluation F U hU _
  let p (v : U∞ × ℝ) := Q.symm (fun i => Q 1 i + v.2 • (Q v.1 i - Q 1 i))
  refine ⟨p, hp.comp (contMDiff_pi_space.mpr fun i => ?_), ?_, ?_⟩
  · exact contMDiff_const.add (contMDiff_snd.smul ((hq i).comp contMDiff_fst |>.sub contMDiff_const))
  · intro v
    simp [p]
  · intro v
    simp [p]

end Langlands.Global.InfiniteAdelicGroupPoints
