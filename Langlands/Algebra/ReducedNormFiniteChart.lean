import Langlands.Algebra.ReducedNorm

/-! Canonical reduced norm in splitting charts with arbitrary finite indices. -/

noncomputable section

namespace Langlands.CentralSimple

universe u uL uI uJ uR

open scoped TensorProduct
open Langlands.ReducedNorm

variable (K A : Type u) [Field K] [Ring A] [Algebra K A]
  [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]
  {L : Type uL} [Field L] [Algebra K L]
  {I : Type uI} [Fintype I] [DecidableEq I]

omit [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A] in
/-- Every finite matrix splitting chart has the canonical reduced degree. -/
theorem card_eq_reducedDegree (e : L ⊗[K] A ≃ₐ[L] Matrix I I L) :
    Fintype.card I = reducedDegree K A :=
  matrix_size_eq_reducedDegree K A L (Fintype.card I)
    (e.trans (Matrix.reindexAlgEquiv L L (Fintype.equivFin I)))

omit [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A] in
/-- Reindex an arbitrary finite splitting chart to the canonical matrix size. -/
def canonicalSizeChart (e : L ⊗[K] A ≃ₐ[L] Matrix I I L) :
    L ⊗[K] A ≃ₐ[L] Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A)) L :=
  e.trans (Matrix.reindexAlgEquiv L L
    ((Fintype.equivFin I).trans (finCongr (card_eq_reducedDegree K A e))))

/-- The canonical reduced norm is determinant in every finite-index chart. -/
theorem reducedNorm_eq_det_fintype (e : L ⊗[K] A ≃ₐ[L] Matrix I I L)
    (R : Type uR) [CommRing R] [Algebra K R] [Algebra L R] [IsScalarTower K L R]
    (x : R ⊗[K] A) :
    reducedNorm K A R x = (splittingMap e R x).det := by
  let q : I ≃ Fin (reducedDegree K A) :=
    (Fintype.equivFin I).trans (finCongr (card_eq_reducedDegree K A e))
  let f := canonicalSizeChart K A e
  have hf : splittingMap f R x = Matrix.reindex q q (splittingMap e R x) := by
    induction x using TensorProduct.inductionOn with
    | tmul r a =>
      simp only [splittingMap_tmul]
      rfl
    | add x y hx hy =>
      simp only [map_add, hx, hy]
      rfl
  rw [reducedNorm_eq_det K A f R x, hf, Matrix.det_reindex_self]

/-- Over its splitting field, a finite-index chart gives the norm directly. -/
theorem reducedNorm_eq_chart_det_fintype (e : L ⊗[K] A ≃ₐ[L] Matrix I I L)
    (x : L ⊗[K] A) :
    reducedNorm K A L x = (e x).det := by
  rw [reducedNorm_eq_det_fintype K A e L]
  congr 1
  induction x using TensorProduct.inductionOn with
  | tmul l a =>
    rw [splittingMap_tmul]
    change l • e (1 ⊗ₜ[K] a) = e (l ⊗ₜ[K] a)
    rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy => simp only [map_add, hx, hy]

section Galois

variable [FiniteDimensional K L] [IsGalois K L] [Nonempty I]
  {J : Type uJ} [Fintype J]

/-- Any finite Galois chart and finite basis give the canonical law on every test algebra. -/
theorem normFromGalois_eq_reducedNorm (b : Module.Basis J K A)
    (e : L ⊗[K] A ≃ₐ[L] Matrix I I L)
    (R : Type uR) [CommRing R] [Algebra K R] (x : R ⊗[K] A) :
    normFromGalois b e R x = reducedNorm K A R x := by
  apply Algebra.TensorProduct.includeRight_injective
    (FaithfulSMul.algebraMap_injective K L)
  rw [← normFromGalois_naturality b e (Algebra.TensorProduct.includeRight (A := L)),
    ← reducedNorm_naturality K A (Algebra.TensorProduct.includeRight (A := L)),
    normFromGalois_eq_det, reducedNorm_eq_det_fintype K A e]

/-- The actual homomorphisms on units agree, for every commutative test algebra. -/
theorem normFromGaloisUnits_eq_reducedNormUnits (b : Module.Basis J K A)
    (e : L ⊗[K] A ≃ₐ[L] Matrix I I L)
    (R : Type uR) [CommRing R] [Algebra K R] :
    normFromGaloisUnits b e R = reducedNormUnits K A R := by
  ext x
  exact normFromGalois_eq_reducedNorm K A b e R x.val

/-- The charted norm-one subgroup is literally the canonical norm-one subgroup. -/
theorem normFromGaloisOne_eq_reducedNormOne (b : Module.Basis J K A)
    (e : L ⊗[K] A ≃ₐ[L] Matrix I I L)
    (R : Type uR) [CommRing R] [Algebra K R] :
    normFromGaloisOne b e R = reducedNormOne K A R := by
  unfold normFromGaloisOne reducedNormOne
  rw [normFromGaloisUnits_eq_reducedNormUnits K A b e R]

end Galois

end Langlands.CentralSimple
