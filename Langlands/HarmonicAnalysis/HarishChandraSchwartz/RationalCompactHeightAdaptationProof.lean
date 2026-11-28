import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCompactHeightAdaptation
import Langlands.BruhatTits.RationalPoints.BoundedSetOperations
import Langlands.GroupScheme.BoundedSubgroupStableLatticeProof
import Langlands.GroupScheme.MatrixRepresentation.CharacterSpanEmbedding
import Langlands.GroupScheme.MatrixRepresentation.RationalDualConjugateIrreducibility
import Langlands.GroupScheme.Rational.SplitRankTransport

/-! # Compact-adapted rational matrix heights -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj Matrix NNReal
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme
open Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology

private theorem residueNorm_coe_integer_le_one (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (x : (ValuativeRel.valuation F).integer) :
    LocalField.residueNormalizedAbsoluteValue F (x : F) ≤ 1 := by
  have hq : (1 : ℝ≥0) < (LocalField.residueCardinality F : ℝ≥0) := by
    exact_mod_cast LocalField.residueCardinality_gt_one F
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
  have hv : FML.normalizedMultiplicativeValuation F (x : F) ≤ 1 := by
    change e (ValuativeRel.valuation F (x : F)) ≤ 1
    rw [← map_one e, map_le_map_iff]
    exact x.property
  have h := (WithZeroMulInt.toNNReal_strictMono hq).monotone hv
  rw [map_one] at h
  exact_mod_cast h

/-- A basis of a compact-stable full lattice makes each matrix and its
inverse integral at the prescribed compact. -/
theorem rationalCompactHeightAdaptation : RationalCompactHeightAdaptationStatement.{u} := by
  intro F _ _ _ _ G _ _ N _ ρ hρ K hK
  classical
  obtain ⟨L, hL⟩ := boundedSubgroupStableLattice F G N ρ K
    (isAlgebraicallyBounded_of_isCompact hK)
  let R := (ValuativeRel.valuation F).integer
  let : Submodule.IsLattice F L := hL.1
  have hdim : Module.finrank R L = N := by
    simpa using (Submodule.IsLattice.finrank_of_pi F L)
  let b := Module.finBasisOfFinrankEq R L hdim
  let bF := b.extendOfIsLattice F
  let g := basisCoordinatePoint bF
  have hB (v : Fin N → F) :
      (basisCoordinateGL bF : Matrix (Fin N) (Fin N) F) *ᵥ v = bF.repr v := by
    change bF.toMatrix (Pi.basisFun F (Fin N)) *ᵥ v = _
    have h := (Pi.basisFun F (Fin N)).toMatrix_mulVec_repr bF v
    rwa [show ((Pi.basisFun F (Fin N)).repr v : Fin N → F) = v from
      funext fun i => by simp] at h
  have hBinv (j : Fin N) :
      (((basisCoordinateGL bF)⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) *ᵥ
        Pi.single j 1 = bF j := by
    change (Pi.basisFun F (Fin N)).toMatrix bF *ᵥ Pi.single j 1 = bF j
    rw [Matrix.mulVec_single_one]
    funext i
    simp only [Matrix.col_apply, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
  have hcoord (v : L) (i : Fin N) :
      bF.repr (v : Fin N → F) i = (b.equivFun v i : F) := by
    have hv : (v : Fin N → F) = ∑ j, (b.equivFun v j : F) • bF j := by
      change (v : Fin N → F) = ∑ j, algebraMap R F (b.equivFun v j) • bF j
      simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower, algebraMap_smul,
        bF, Module.Basis.extendOfIsLattice_apply] using
          (congrArg (fun w : L => (w : Fin N → F)) (b.sum_equivFun v)).symm
    rw [hv, Module.Basis.repr_sum_self]
  refine ⟨g, hρ.comp_iso ((GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)).innerIso g), ?_⟩
  have hentry (x : rationalPoints G) (hx : x ∈ K) (i j : Fin N) :
      LocalField.residueNormalizedAbsoluteValue F
        (((ρ.conjugate g).rationalMatrix x : Matrix (Fin N) (Fin N) F) i j) ≤ 1 := by
    have hj : bF j ∈ L := by
      simpa only [bF, Module.Basis.extendOfIsLattice_apply] using (b j).property
    let v : L := ⟨(ρ.rationalMatrix x : Matrix (Fin N) (Fin N) F) *ᵥ (bF j),
      hL.2 x hx (bF j) hj⟩
    have hcol :
        ((ρ.conjugate g).rationalMatrix x : Matrix (Fin N) (Fin N) F) *ᵥ Pi.single j 1 =
          bF.repr (v : Fin N → F) := by
      rw [conjugate_rationalMatrix, show g = basisCoordinatePoint bF from rfl,
        rationalMatrix_basisCoordinatePoint]
      rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hBinv, hB]
    have he := congrFun hcol i
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at he
    change (((ρ.conjugate g).rationalMatrix x : Matrix (Fin N) (Fin N) F) i j) =
      bF.repr (v : Fin N → F) i at he
    rw [he, hcoord]
    exact residueNorm_coe_integer_le_one F _
  intro x hx
  change rationalMatrixNorm F (ρ.conjugate g) x ≤ 1
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  change glNorm ((ρ.conjugate g).rationalMatrix x) ≤ 1
  apply glNorm_le (hentry x hx)
  intro i j
  change LocalField.residueNormalizedAbsoluteValue F
    (((((ρ.conjugate g).rationalMatrix x)⁻¹ : GL (Fin N) F) :
      Matrix (Fin N) (Fin N) F) i j) ≤ 1
  rw [← map_inv]
  exact hentry x⁻¹ (K.inv_mem hx) i j

end Langlands.HarishChandraSchwartz
