import Langlands.GroupScheme.Rational.RealApproximationReductiveReductionStatement
import Langlands.AlgebraicGeometry.PointTopology.RealApproximation
import Langlands.GroupScheme.Reductive.CharacteristicZeroLeviProof
import Langlands.GroupScheme.Unipotent.PerfectFieldSplitProof
import Langlands.GroupScheme.Unipotent.SplitAffineSpaceProof

/-! # Real approximation reduced to connected reductive groups -/

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

/-- The characteristic-zero Levi decomposition reduces real approximation to
connected reductive groups over the rationals. -/
theorem realApproximationReductiveReduction :
    RealApproximationReductiveReductionStatement := by
  intro hred G _ hGsm hGc
  let : Smooth G.X.hom := hGsm
  obtain ⟨L, p, j, hjp, hL, hUsm, hUc, hUu⟩ :=
    characteristicZeroLeviDecomposition ℚ G hGsm hGc
  let : IsAffineHom L.X.hom := hL.isAffineHom
  let : IsAffine L.X.left := isAffine_of_isAffineHom L.X.hom
  let : Smooth L.X.hom := hL.smooth
  let : Smooth (kernel p).X.hom := hUsm
  let : IsAffine (kernel p).X.left :=
    IsAffine.of_isPullback (kernel_isPullback_scheme p)
  let : IsAffineHom (kernel p).X.hom := inferInstance
  have hUsplit := perfectFieldUnipotentSplit ℚ (kernel p) hUc hUu
  obtain ⟨n, hn⟩ := hUsplit
  obtain ⟨e⟩ := splitUnipotentAffineSpaceStatement ℚ n (kernel p) inferInstance hn
  let : IsAffine
      (Over.mk (𝔸(ULift (Fin n); Spec (CommRingCat.of ℚ)) ↘ Spec (CommRingCat.of ℚ))).left :=
    IsAffine.of_isIso (AffineSpace.SpecIso (ULift (Fin n)) (CommRingCat.of ℚ)).hom
  have hU : HasRealApproximation (kernel p).X :=
    (hasRealApproximation_affineSpace (ULift (Fin n))).of_iso e.symm
  have hLr : HasRealApproximation L.X := hred L hL
  let : IsAffine ((kernel p).X ⊗ L.X).left :=
    tensor_isAffine ℚ (kernel p).X L.X
  let f : (kernel p).X ⊗ L.X ⟶ G.X :=
    (fst (kernel p).X L.X ≫ (kernelι p).hom.hom) *
      (snd (kernel p).X L.X ≫ j.hom.hom)
  apply (hU.tensor hLr).map f
  intro g
  let l : RingPoint ℚ L.X ℝ := g ≫ p.hom.hom
  let a : RingPoint ℚ G.X ℝ := g * (l ≫ j.hom.hom)⁻¹
  have hjp' : j.hom.hom ≫ p.hom.hom = 𝟙 L.X :=
    congrArg (fun q => q.hom.hom) hjp
  have ha : a ≫ p.hom.hom = 1 := by
    dsimp only [a]
    rw [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, hjp',
      Category.comp_id]
    exact mul_inv_cancel _
  let k : RingPoint ℚ (kernel p).X ℝ :=
    (kernel_isPullback p).lift a (toUnit (ringTest ℚ ℝ)) ha
  have hk : k ≫ (kernelι p).hom.hom = a :=
    (kernel_isPullback p).lift_fst _ _ _
  refine ⟨lift k l, ?_⟩
  change lift k l ≫ f = g
  dsimp only [f]
  rw [MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, hk]
  exact inv_mul_cancel_right g (l ≫ j.hom.hom)

end Langlands.GroupScheme
