import Langlands.GroupScheme.Dynamic.AdjointDeterminantLine
import Langlands.GroupScheme.MatrixRepresentation.CharacterSpanEmbedding
import Langlands.GroupScheme.MatrixRepresentation.IntertwinerTransport
import Langlands.GroupScheme.MatrixRepresentation.Reindex
import Langlands.GroupScheme.MatrixRepresentation.SplitTorusCharacterDecomposition
import Langlands.GroupScheme.Rational.FundamentalRepresentations
import Langlands.GroupScheme.Rational.IndependentWeightProductProof
import Langlands.GroupScheme.Reductive.DominantMultipleExterior

/-! # Weight bases for scalar-extended exterior representations -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Module
open scoped Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

variable {K : Type u} [Field K] {n j : ℕ} {l : Type} [Fintype l] [DecidableEq l]

/-- The exterior basis in the reindexed standard coordinates. -/
def reindexedExteriorBasis (b : Basis (Fin n) K (Fin n → K))
    (e : Set.powersetCard (Fin n) j ≃ l) : Basis l K (l → K) :=
  let U := Chevalley.reindexGL e (Chevalley.exteriorGL n j K (basisCoordinateGL b))
  (Pi.basisFun K l).map (Matrix.GeneralLinearGroup.toLin U⁻¹).toLinearEquiv

theorem reindexedExteriorBasis_apply (b : Basis (Fin n) K (Fin n → K))
    (e : Set.powersetCard (Fin n) j ≃ l) (i r : l) :
    reindexedExteriorBasis b e i r =
      ((Chevalley.reindexGL e (Chevalley.exteriorGL n j K (basisCoordinateGL b)))⁻¹ :
        GL l K).val r i := by
  rw [reindexedExteriorBasis, Basis.map_apply]
  change ((_ : Matrix l l K) *ᵥ (Pi.basisFun K l i)) r = _
  rw [Pi.basisFun_apply, Matrix.mulVec_single_one, Matrix.col_apply]

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.GroupScheme.SplitPinning

open MatrixRepresentation

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n j : ℕ} {l : Type} [Fintype l] [DecidableEq l]

local notation "G_K" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) G

local instance : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

set_option maxHeartbeats 1200000 in
/-- The exterior basis of the scalar extension has the sums of the selected weights. -/
theorem reindexedExteriorBasis_mem_representationWeightSpace
    (p : SplitPinning (k := K) G_K) (ρ : MatrixRepresentation G (Fin n))
    (b : Basis (Fin n) K (Fin n → K)) (w : Fin n → characterLattice p.torus)
    (hb : ∀ i, b i ∈ p.representationWeightSpace (ρ.baseChange (algebraBaseMap k K)) (w i))
    (e : Set.powersetCard (Fin n) j ≃ l) (i : l) :
    reindexedExteriorBasis b e i ∈ p.representationWeightSpace
      (((Chevalley.exteriorRepresentation n j (CommRingCat.of k) ρ).reindex e).baseChange
        (algebraBaseMap k K)) (∑ a ∈ (e.symm i).val, w a) := by
  let := p.isSplitTorus.isAffineHom
  let χ := (rationalCharacters.equivCharacterLattice p.torus).symm
  let ρK := ρ.baseChange (algebraBaseMap k K)
  let τ := (Chevalley.exteriorRepresentation n j (CommRingCat.of k) ρ).reindex e
  change reindexedExteriorBasis b e i ∈
    ((τ.baseChange (algebraBaseMap k K)).restrict p.inclusion).characterSpace
      (χ (∑ a ∈ (e.symm i).val, w a))
  rw [mem_characterSpace_iff_affine]
  intro A t
  rw [affineMatrix_restrict]
  let x : GroupScheme.affinePoints G_K A := t ≫ p.inclusion.hom.hom
  let M := ρK.affineMatrix A x
  let B := Matrix.GeneralLinearGroup.map (algebraMap K A) (basisCoordinateGL b)
  let f : GL (Fin n) A →* GL l A :=
    (Chevalley.reindexGL e).comp (Chevalley.exteriorGL n j A)
  let U := f B
  let D : Matrix l l A :=
    Matrix.diagonal (fun s => (Lie.characterValue (∑ a ∈ (e.symm s).val, w a) t : A))
  have hτ : ((τ.baseChange (algebraBaseMap k K)).affineMatrix A x : Matrix l l A) = f M := by
    let : Algebra k A := Algebra.compHom A (algebraMap k K)
    let : IsScalarTower k K A := IsScalarTower.of_algebraMap_eq' rfl
    have hM : (M : Matrix (Fin n) (Fin n) A) =
        ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) A)
          (Lie.affineBaseChangeEquiv k K G A x) :=
      affineMatrix_baseChange_fintype ρ A x
    rw [affineMatrix_baseChange_fintype]
    change ((τ.affineMatrix (CommAlgCat.of (CommRingCat.of k) A)
      (Lie.affineBaseChangeEquiv k K G A x)) : Matrix l l A) = _
    rw [reindex_affineMatrix, Chevalley.exteriorRepresentation_affineMatrix]
    exact congrArg (fun m : GL (Fin n) A => (f m : Matrix l l A)) (Units.ext hM.symm)
  have hB : (↑(B * M * B⁻¹) : Matrix (Fin n) (Fin n) A) =
      Matrix.diagonal (fun a => (Lie.characterValue (w a) t : A)) := by
    have h := conjugate_basisCoordinatePoint_affineMatrix (ρK.restrict p.inclusion)
      b (fun a => χ (w a)) hb A t
    rw [conjugate_affineMatrix, affineMatrix_constantPoint, rationalMatrix_basisCoordinatePoint,
      affineMatrix_restrict] at h
    exact h
  have hprod (s : Finset (Fin n)) :
      (Lie.characterValue (∑ a ∈ s, w a) t : A) =
        ∏ a ∈ s, (Lie.characterValue (w a) t : A) := by
    classical
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty, IndependentWeightProduct.characterValue_zero, Units.val_one,
        Finset.prod_empty]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, IndependentWeightProduct.characterValue_add, Units.val_mul,
        Finset.prod_insert ha, ih]
  have hD : (↑(f (B * M * B⁻¹)) : Matrix l l A) = D := by
    change (Chevalley.reindexGL e (Chevalley.exteriorGL n j A (B * M * B⁻¹)) : Matrix l l A) = D
    rw [reindexGL_val, Chevalley.exteriorGL_diagonal _ _ hB, Matrix.submatrix_diagonal_equiv]
    exact congrArg Matrix.diagonal (funext fun s => (hprod (e.symm s).val).symm)
  have hconj : (↑U : Matrix l l A) * (f M : Matrix l l A) * (↑U⁻¹ : Matrix l l A) = D := by
    simpa only [map_mul, map_inv, Matrix.GeneralLinearGroup.coe_mul, U] using hD
  have hcol : (f M : Matrix l l A) * (↑U⁻¹ : Matrix l l A) = (↑U⁻¹ : Matrix l l A) * D := by
    have hcancel : (↑U⁻¹ : Matrix l l A) * (↑U : Matrix l l A) = 1 :=
      congrArg (fun V : GL l A => V.val) (inv_mul_cancel U)
    rw [← hconj, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hcancel, Matrix.one_mul]
  have hU : U = Matrix.GeneralLinearGroup.map (algebraMap K A)
      (Chevalley.reindexGL e (Chevalley.exteriorGL n j K (basisCoordinateGL b))) := by
    change Chevalley.reindexGL e (Chevalley.exteriorGL n j A B) = _
    rw [Chevalley.exteriorGL_naturality, reindexGL_map]
  have hv (r : l) : algebraMap K A (reindexedExteriorBasis b e i r) =
      (U⁻¹ : GL l A).val r i := by
    rw [reindexedExteriorBasis_apply, hU, ← map_inv]
    rfl
  change ((τ.baseChange (algebraBaseMap k K)).affineMatrix A x : Matrix l l A) *ᵥ
      (fun r => algebraMap K A (reindexedExteriorBasis b e i r)) =
    (Lie.characterValue (∑ a ∈ (e.symm i).val, w a) t : A) •
      (fun r => algebraMap K A (reindexedExteriorBasis b e i r))
  rw [hτ]
  simp only [hv]
  funext r
  have h := congrArg (fun L : Matrix l l A => L r i) hcol
  rw [Matrix.mul_diagonal] at h
  simpa only [Matrix.mul_apply, Matrix.mulVec_apply_eq_sum, D, Function.comp_apply,
    Pi.smul_apply, smul_eq_mul, mul_comm] using h

end Langlands.GroupScheme.SplitPinning
