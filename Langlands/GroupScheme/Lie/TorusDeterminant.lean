import Langlands.GroupScheme.Lie.FiniteCoordinateScalarExtension
import Langlands.GroupScheme.Torus.FiniteCoordinateWeightDecomposition
import Langlands.GroupScheme.Lie.ActionDeterminant
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Weight bases and determinants of actual split-torus Lie actions -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.AutomorphicAction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k] {H U : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom U.X.hom] (a : AutomorphicAction H U) {d : ℕ}
    (c : Lie.FiniteCoordinates U d) {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT : IsSplitTorus T.toGrp) (j : T.toGrp ⟶ H)

include c hT in
/-- There are finitely many nonzero actual character weight spaces. -/
theorem finite_lieWeightSupport_of_finiteCoordinates :
    Set.Finite {α : characterLattice T | a.lieWeightSpace j α ≠ ⊥} := by
  classical
  let : FiniteDimensional k (Additive (lieKernel U k)) :=
    (c.equiv (.of (CommRingCat.of k) k)).symm.finiteDimensional
  exact Submodule.finite_ne_bot_of_iSupIndep
    (R := k) (M := Additive (lieKernel U k))
    (isInternal_lieWeightSpace_of_finiteCoordinates k U c T hT a j).submodule_iSupIndep

include c hT in
/-- The actual nonzero roots are finite, with no finite-type assumption. -/
theorem finite_lieRoots_of_finiteCoordinates : (a.lieRoots j).Finite :=
  (a.finite_lieWeightSupport_of_finiteCoordinates c hT j).subset (fun _ h => h.2)

/-- Each occurring character is repeated according to its actual weight-space dimension. -/
def lieWeightBasisIndex :=
  Σ α : {α : characterLattice T | a.lieWeightSpace j α ≠ ⊥},
    Fin (Module.finrank k (a.lieWeightSpace j α.val))

/-- A basis of the actual base Lie kernel assembled from bases of the nonzero weight spaces. -/
def lieWeightBasis : Module.Basis (a.lieWeightBasisIndex j) k (Additive (lieKernel U k)) := by
  classical
  let : FiniteDimensional k (Additive (lieKernel U k)) :=
    (c.equiv (.of (CommRingCat.of k) k)).symm.finiteDimensional
  exact (DirectSum.isInternal_ne_bot_iff.mpr
    (isInternal_lieWeightSpace_of_finiteCoordinates k U c T hT a j)).collectedBasis
      (fun α => Module.finBasis k (a.lieWeightSpace j α.val))

/-- Every collected basis vector has its indexed character weight. -/
theorem lieWeightBasis_mem (i : a.lieWeightBasisIndex j) :
    a.lieWeightBasis c hT j i ∈ a.lieWeightSpace j i.1.val := by
  classical
  let : FiniteDimensional k (Additive (lieKernel U k)) :=
    (c.equiv (.of (CommRingCat.of k) k)).symm.finiteDimensional
  exact DirectSum.IsInternal.collectedBasis_mem
    (DirectSum.isInternal_ne_bot_iff.mpr
      (isInternal_lieWeightSpace_of_finiteCoordinates k U c T hT a j))
    (fun α => Module.finBasis k (a.lieWeightSpace j α.val)) i

include c hT in
/-- The collected basis has finite index type. -/
theorem finite_lieWeightBasisIndex : Finite (a.lieWeightBasisIndex j) := by
  let := (a.finite_lieWeightSupport_of_finiteCoordinates c hT j).fintype
  unfold lieWeightBasisIndex
  infer_instance

/-- In the extended weight basis every actual differential is diagonal. -/
theorem differential_toMatrix_lieWeightBasis
    [Fintype (a.lieWeightBasisIndex j)] [DecidableEq (a.lieWeightBasisIndex j)]
    (A : CommAlgCat.{u} (CommRingCat.of k))
    (t : Lie.AffinePoints T.toGrp A) :
    LinearMap.toMatrix (c.baseChangeBasis (a.lieWeightBasis c hT j) A)
      (c.baseChangeBasis (a.lieWeightBasis c hT j) A)
      (a.differential (t ≫ j.hom.hom)).toLinearMap =
      Matrix.diagonal (fun i : a.lieWeightBasisIndex j =>
        (Lie.characterValue i.1.val t : A)) := by
  let b := c.baseChangeBasis (a.lieWeightBasis c hT j) A
  have he (i : a.lieWeightBasisIndex j) :
      a.differential (t ≫ j.hom.hom) (b i) =
        (Lie.characterValue i.1.val t : A) • b i := by
    simpa only [b, Lie.FiniteCoordinates.baseChangeBasis_apply] using
      (a.lieWeightBasis_mem c hT j i) A t
  ext i l
  rw [LinearMap.toMatrix_apply]
  change b.repr (a.differential (t ≫ j.hom.hom) (b l)) i = _
  rw [he l, map_smul]
  by_cases h : i = l
  · subst l
    simp
  · simp [h]

include c hT in
/-- The actual Lie determinant is the product of the collected basis characters. -/
theorem differential_det_lieWeightBasis
    [Fintype (a.lieWeightBasisIndex j)] [DecidableEq (a.lieWeightBasisIndex j)]
    (A : CommAlgCat.{u} (CommRingCat.of k))
    (t : Lie.AffinePoints T.toGrp A) :
    LinearEquiv.det (a.differential (t ≫ j.hom.hom)) =
      ∏ i : a.lieWeightBasisIndex j, Lie.characterValue i.1.val t := by
  apply Units.ext
  rw [LinearEquiv.coe_det,
    ← LinearMap.det_toMatrix (c.baseChangeBasis (a.lieWeightBasis c hT j) A),
    a.differential_toMatrix_lieWeightBasis c hT j A t, Matrix.det_diagonal]
  simp

end Langlands.GroupScheme.AutomorphicAction
