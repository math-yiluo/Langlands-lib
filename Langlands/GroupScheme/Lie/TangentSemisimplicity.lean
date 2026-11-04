import Langlands.GroupScheme.Lie.RepresentationDifferential
import Langlands.GroupScheme.Lie.RepresentationSubquotient
import Langlands.GroupScheme.Chevalley.RepresentationExtension
import Langlands.GroupScheme.MatrixRepresentationTensor
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly

/-! # Tangent matrix operations and semisimplicity over an algebraically closed field -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj Matrix TensorProduct

namespace Langlands.GroupScheme.Lie

/-- The scalar extension to an algebraic closure is an equivalence when the base
field is already algebraically closed. -/
def algebraicClosureBaseEquiv (k : Type u) [Field k] [IsAlgClosed k] :
    k ≃ₐ[k] AlgebraicClosure k :=
  AlgEquiv.ofBijective (Algebra.ofId k (AlgebraicClosure k))
    IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- Geometric matrix semisimplicity is ordinary semisimplicity over an
algebraically closed base field. -/
theorem IsGeometricallySemisimpleMatrix.isSemisimple
    {k : Type u} [Field k] [IsAlgClosed k]
    {n : Type} [Fintype n] [DecidableEq n] {M : Matrix n n k}
    (hM : IsGeometricallySemisimpleMatrix M) :
    Module.End.IsSemisimple (Matrix.toLin' M) := by
  let e := algebraicClosureBaseEquiv k
  let E : (AlgebraicClosure k)[X] ≃+* k[X] := Polynomial.mapEquiv e.symm.toRingEquiv
  let q := minpoly (AlgebraicClosure k) (M.map (algebraMap k (AlgebraicClosure k)))
  have hq : Squarefree q := by
    simpa only [Matrix.minpoly_toLin'] using hM.minpoly_squarefree
  have hp : Squarefree (E q) := by
    intro r hr
    have hh : E.symm r * E.symm r ∣ q := by
      simpa using map_dvd E.symm hr
    simpa using (hq _ hh).map E.toMonoidHom
  have he : (M.map (algebraMap k (AlgebraicClosure k))).map e.symm = M := by
    ext i j
    exact e.symm_apply_apply (M i j)
  have hc : (algebraMap k (Matrix n n k)).comp e.symm.toRingHom =
      e.symm.toRingHom.mapMatrix.comp
        (algebraMap (AlgebraicClosure k) (Matrix n n (AlgebraicClosure k))) := by
    ext a i j
    by_cases h : i = j <;> simp [h, Matrix.algebraMap_matrix_apply]
  have hz := map_aeval_eq_aeval_map hc q
    (M.map (algebraMap k (AlgebraicClosure k)))
  rw [minpoly.aeval, map_zero] at hz
  change 0 = aeval ((M.map (algebraMap k (AlgebraicClosure k))).map e.symm) (E q) at hz
  rw [he] at hz
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hp
  calc
    _ = Matrix.toLinAlgEquiv'.toAlgHom (aeval M (E q)) :=
      aeval_algHom_apply Matrix.toLinAlgEquiv'.toAlgHom M (E q)
    _ = 0 := by rw [← hz, map_zero]

end Langlands.GroupScheme.Lie

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The actual dual-number representation matrix is reconstructed from its tangent matrix. -/
theorem affineMatrix_eq_matrixUnit (ρ : MatrixRepresentation G n) (X : lieKernel G k) :
    ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) (DualNumber k)) X.val =
      GeneralLinear.DualNumber.matrixUnit (ρ.tangentMatrix k X) := by
  have h := congrArg (fun Y : lieKernel (GeneralLinear.groupScheme n (CommRingCat.of k)) k =>
    GeneralLinear.affinePointsEquiv n (CommRingCat.of k)
      (CommAlgCat.of (CommRingCat.of k) (DualNumber k)) Y.val)
    (ρ.pointKernelEquiv_tangentMatrix k X)
  change GeneralLinear.affinePointsEquiv n (CommRingCat.of k)
      (CommAlgCat.of (CommRingCat.of k) (DualNumber k))
      (GeneralLinear.DualNumber.pointUnit (ρ.tangentMatrix k X)) =
    ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) (DualNumber k)) X.val at h
  rw [GeneralLinear.DualNumber.pointUnit_matrix] at h
  exact h.symm

/-- The constant coefficients of the matrix of an actual tangent point are the identity. -/
theorem affineMatrix_fst (ρ : MatrixRepresentation G n) (X : lieKernel G k) (i j : n) :
    (ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) (DualNumber k)) X.val i j).fst =
      (1 : Matrix n n k) i j := by
  rw [affineMatrix_eq_matrixUnit]
  by_cases h : i = j <;>
    simp [GeneralLinear.DualNumber.matrixUnit, GeneralLinear.DualNumber.epsilonMatrix,
      Matrix.one_apply, h]

/-- The dual differential is minus the transpose of the original differential. -/
theorem tangentMatrix_dual (ρ : MatrixRepresentation G n) (X : lieKernel G k) :
    ρ.dual.tangentMatrix k X = -(ρ.tangentMatrix k X).transpose := by
  ext i j
  change (ρ.dual.affineMatrix (CommAlgCat.of (CommRingCat.of k) (DualNumber k))
    X.val i j).snd = _
  rw [dual_affineMatrix, GeneralLinear.matrixContragredient_coe,
    affineMatrix_eq_matrixUnit]
  change (((GeneralLinear.DualNumber.matrixUnit (ρ.tangentMatrix k X))⁻¹ :
    GL n (DualNumber k)).val j i).snd = -ρ.tangentMatrix k X j i
  rw [GeneralLinear.DualNumber.matrixUnit_inv_val]
  by_cases h : j = i <;>
    simp [GeneralLinear.DualNumber.epsilonMatrix, h]

/-- Epsilon coefficients of tensor representations satisfy the ordinary tensor differential law. -/
theorem tangentMatrix_tensor_entry (ρ : MatrixRepresentation G n)
    (σ : MatrixRepresentation G m) (X : lieKernel G k) (i l : n) (j s : m) :
    (ρ.tensor σ).tangentMatrix k X (i, j) (l, s) =
      (1 : Matrix n n k) i l * σ.tangentMatrix k X j s +
        ρ.tangentMatrix k X i l * (1 : Matrix m m k) j s := by
  change ((ρ.tensor σ).affineMatrix
    (CommAlgCat.of (CommRingCat.of k) (DualNumber k)) X.val (i, j) (l, s)).snd = _
  rw [tensor_affineMatrix_entry]
  change
    (ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) (DualNumber k)) X.val i l).fst *
        (σ.affineMatrix (CommAlgCat.of (CommRingCat.of k) (DualNumber k)) X.val j s).snd +
      (ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) (DualNumber k)) X.val i l).snd *
        (σ.affineMatrix (CommAlgCat.of (CommRingCat.of k) (DualNumber k)) X.val j s).fst = _
  rw [affineMatrix_fst, affineMatrix_fst]
  rfl

/-- Tangent matrices respect the actual finite reindexing representation. -/
theorem tangentMatrix_reindex (ρ : MatrixRepresentation G n) (e : n ≃ m)
    (X : lieKernel G k) :
    (Chevalley.reindexRepresentation e (CommRingCat.of k) ρ).tangentMatrix k X =
      Matrix.reindex e e (ρ.tangentMatrix k X) := by
  ext i j
  change ((Chevalley.reindexRepresentation e (CommRingCat.of k) ρ).affineMatrix
    (CommAlgCat.of (CommRingCat.of k) (DualNumber k)) X.val i j).snd = _
  rw [Chevalley.reindexRepresentation_affineMatrix]
  rfl

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.GroupScheme.Lie

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Representation-tested semisimplicity applies to every finite indexing type. -/
theorem IsSemisimpleElement.isSemisimple_tangentMatrix
    {X : lieKernel G k} (hX : IsSemisimpleElement G X)
    {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n) :
    Module.End.IsSemisimple (Matrix.toLin' (ρ.tangentMatrix k X)) := by
  let e := Fintype.equivFin n
  have h := (hX _ (Chevalley.reindexRepresentation e (CommRingCat.of k) ρ)).isSemisimple
  rw [MatrixRepresentation.tangentMatrix_reindex] at h
  let E := LinearEquiv.funCongrLeft k k e.symm
  apply isSemisimple_of_injective_intertwiner E.toLinearMap E.injective _ h
  change E.toLinearMap ∘ₗ (ρ.tangentMatrix k X).mulVecLin =
    (Matrix.reindex e e (ρ.tangentMatrix k X)).mulVecLin ∘ₗ E.toLinearMap
  rw [Matrix.mulVecLin_reindex]
  apply LinearMap.ext
  intro v
  funext i
  change (ρ.tangentMatrix k X *ᵥ v) (e.symm i) =
    (ρ.tangentMatrix k X *ᵥ (fun j => v (e.symm (e j)))) (e.symm i)
  simp only [Equiv.symm_apply_apply]

end Langlands.GroupScheme.Lie
