import Langlands.Algebra.BrauerSplitting
import Langlands.Shimura.Unitary.PlaceTensorDecomposition
import Langlands.Shimura.Unitary.UnitaryLocalProfileRealizationStatement

/-! # Matrix charts over the actual completed quadratic center -/

noncomputable section

universe u v w

namespace Langlands.Shimura.FiniteUnitary

open NumberField Langlands.Global Langlands.Global.AdelicFunctoriality
open scoped TensorProduct FiniteExtension

variable {E : Type u} {K : Type v}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K]
  [Algebra E K] [Algebra.IsQuadraticExtension E K]
  {A : Type w} [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
  {n : ℕ}

omit [NumberField E] [IsScalarTower E K A] in
private theorem exists_completedMatrixChart
    (D : CentralSimpleUnitaryData E K A n) (q : Langlands.Global.FinitePlace K)
    (h : HasCompletedBrauerInvariant K A q 0) :
    Nonempty (CompletedAlgebra K A q ≃ₐ[FiniteCompletion K q]
      Matrix (Fin n) (Fin n) (FiniteCompletion K q)) := by
  obtain ⟨B, ⟨e⟩, hB⟩ := h
  have hz : Brauer.classOf B = 0 :=
    (finiteBrauerInvariant K q).injective (hB.trans (map_zero _).symm)
  obtain ⟨m, -, ⟨f⟩⟩ := (Brauer.classOf_eq_zero_iff B).mp hz
  let : FiniteDimensional K A := D.finite
  have hdim : m * m = n * n := by
    have h := (e.trans f).toLinearEquiv.finrank_eq
    rwa [Module.finrank_baseChange, D.dimension, Module.finrank_matrix, Fintype.card_fin,
      Module.finrank_self, mul_one, pow_two, eq_comm] at h
  have hm : m = n := by nlinarith
  subst m
  exact ⟨e.trans f⟩

variable (p : Langlands.Global.FinitePlace E)

local notation "F" => FiniteCompletion E p
local notation "Q" => FinitePlacesAbove K p

private theorem completedAlgebraCoordinate (x : LocalAlgebra E A p) (q : Q) :
    PlaceTensor.placeTensorEquiv (K := K) p A x q = toCompletedAlgebra E K A p q.val x := by
  induction x using TensorProduct.inductionOn with
  | tmul s a => rw [PlaceTensor.placeTensorEquiv_tmul, toCompletedAlgebra_tmul]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

private def completedProductAlgEquiv :
    LocalAlgebra E A p ≃ₐ[F] (∀ q : Q, CompletedAlgebra K A q.val) :=
  AlgEquiv.ofRingEquiv (f := PlaceTensor.placeTensorEquiv (K := K) p A)
    (fun s => funext fun q => (completedAlgebraCoordinate p _ q).trans
      ((toCompletedAlgebra E K A p q.val).commutes s))

private theorem completedCenterCoordinate (z : LocalCenter E K p) (q : Q) :
    finiteTensorMap (L := K) p z q = completedCenterMap E K p q.val z := by
  induction z using TensorProduct.inductionOn with
  | tmul s k => rw [finiteTensorMap_tmul, completedCenterMap_tmul]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

/-- If every completed central simple factor is split, the actual finite
scalar extension is a matrix algebra over the entire quadratic center. -/
def finiteMatrixChartOfZeroInvariants (D : CentralSimpleUnitaryData E K A n)
    (hz : ∀ q : Q, HasCompletedBrauerInvariant K A q.val 0) :
    { e : LocalAlgebra E A p ≃ₐ[F] Matrix (Fin n) (Fin n) (LocalCenter E K p) //
      ∀ z : LocalCenter E K p, e (localCenterMap E K A p z) = Matrix.scalar (Fin n) z } := by
  let f (q : Q) := (exists_completedMatrixChart D q.val (hz q)).some
  let C := AlgEquiv.ofBijective (finiteTensorMap (L := K) p) ((completedTensorComparison E K).1 p)
  let P := (completedProductAlgEquiv (A := A) p).trans
    (AlgEquiv.piCongrRight fun q : Q => (f q).restrictScalars F)
  let G : Matrix (Fin n) (Fin n) (LocalCenter E K p) ≃ₐ[F]
      (∀ q : Q, Matrix (Fin n) (Fin n) (FiniteCompletion K q.val)) :=
    C.mapMatrix.trans (Matrix.piAlgEquiv F)
  refine ⟨P.trans G.symm, fun z => ?_⟩
  apply G.injective
  change G (G.symm (P (localCenterMap E K A p z))) = G (Matrix.scalar (Fin n) z)
  rw [G.apply_symm_apply]
  funext q
  change f q (PlaceTensor.placeTensorEquiv (K := K) p A (localCenterMap E K A p z) q) = _
  rw [completedAlgebraCoordinate, toCompletedAlgebra_center, (f q).commutes]
  apply Matrix.ext
  intro i j
  change Matrix.scalar (Fin n) (completedCenterMap E K p q.val z) i j =
    finiteTensorMap (L := K) p (Matrix.scalar (Fin n) z i j) q
  by_cases h : i = j <;> simp [Matrix.scalar_apply, h, completedCenterCoordinate]

end Langlands.Shimura.FiniteUnitary
