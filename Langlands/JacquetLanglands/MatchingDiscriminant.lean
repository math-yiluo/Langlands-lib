import Langlands.BaseChange.OrdinaryWeylDifferential
import Langlands.GroupScheme.NormOneOuterDescent
import Langlands.LinearAlgebra.MatrixSquarefreeCharpolyConjugacy

/-! # Adjoint discriminants of matching regular elements -/

noncomputable section

namespace Langlands.JacquetLanglands

open Langlands.BaseChange Langlands.CentralSimple
open scoped TensorProduct

universe u

section Algebra

variable (F : Type*) [Field F] {A : Type*} [Ring A] [Algebra F A]

/-- Conjugation by a unit minus the identity on the ambient algebra. -/
def unitAdjointDefect (g : Aˣ) : Module.End F A :=
  (LinearMap.mulLeft F g.val).comp (LinearMap.mulRight F g⁻¹.val) - LinearMap.id

theorem unitAdjointDefect_apply (g : Aˣ) (x : A) :
    unitAdjointDefect F g x = g.val * x * g⁻¹.val - x := by
  change g.val * (x * g⁻¹.val) - x = _
  rw [mul_assoc]

private theorem unitAdjointDefect_conj {B : Type*} [Ring B] [Algebra F B]
    (e : A ≃ₐ[F] B) (g : Aˣ) :
    e.toLinearEquiv.conj (unitAdjointDefect F g) =
      unitAdjointDefect F (Units.map e.toMonoidHom g) := by
  ext x
  rw [LinearEquiv.conj_apply_apply]
  change e (unitAdjointDefect F g (e.symm x)) =
    unitAdjointDefect F (Units.map e.toMonoidHom g) x
  rw [unitAdjointDefect_apply, unitAdjointDefect_apply]
  change e (g.val * e.symm x * g⁻¹.val - e.symm x) =
    e g.val * x * e g⁻¹.val - x
  rw [map_sub, map_mul, map_mul, AlgEquiv.apply_symm_apply]

private theorem unitAdjointDefect_baseChange (L : Type*) [Field L] [Algebra F L]
    (g : Aˣ) :
    (unitAdjointDefect F g).baseChange L =
      unitAdjointDefect L (Units.map (Algebra.TensorProduct.includeRight : A →ₐ[F]
        L ⊗[F] A).toMonoidHom g) := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
    rw [LinearMap.baseChange_tmul, unitAdjointDefect_apply, unitAdjointDefect_apply,
      TensorProduct.tmul_sub]
    change a ⊗ₜ[F] (g.val * x * g⁻¹.val) - a ⊗ₜ[F] x =
      (1 ⊗ₜ[F] g.val) * (a ⊗ₜ[F] x) * (1 ⊗ₜ[F] g⁻¹.val) - a ⊗ₜ[F] x
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

private theorem charpoly_unitAdjointDefect_map [FiniteDimensional F A]
    {L : Type*} [Field L] [Algebra F L] {B : Type*} [Ring B] [Algebra L B]
    [FiniteDimensional L B] (e : L ⊗[F] A ≃ₐ[L] B) (g : Aˣ) :
    (unitAdjointDefect F g).charpoly.map (algebraMap F L) =
      (unitAdjointDefect L (Units.map e.toMonoidHom
        (Units.map (Algebra.TensorProduct.includeRight : A →ₐ[F]
          L ⊗[F] A).toMonoidHom g))).charpoly := by
  rw [← LinearMap.charpoly_baseChange, unitAdjointDefect_baseChange,
    ← unitAdjointDefect_conj L e, LinearEquiv.charpoly_conj]

end Algebra

section Matching

variable {F : Type u} [Field F] {D : Type u} [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D] [Algebra.IsCentral F D] {n : ℕ}

private def matrixScalarChart (L : Type*) [Field L] [Algebra F L] :
    L ⊗[F] Matrix (Fin n) (Fin n) F ≃ₐ[L] Matrix (Fin n) (Fin n) L :=
  AlgEquiv.ofRingEquiv (f := (matrixEquivTensor (Fin n) F L).symm.toRingEquiv) fun a => by
    change (matrixEquivTensor (Fin n) F L).symm (a ⊗ₜ[F] (1 : Matrix (Fin n) (Fin n) F)) = _
    rw [matrixEquivTensor_apply_symm, Matrix.map_one _ (map_zero _) (map_one _),
      Algebra.algebraMap_eq_smul_one]

/-- Matching regular elements have the same characteristic polynomial for
conjugation minus the identity on their ambient algebras. -/
theorem Corresponds.adjointDefect_charpoly_eq {g : GeneralLinear n F} {g' : Dˣ}
    (h : Corresponds F D g g') :
    (adjointDefect g).charpoly = (unitAdjointDefect F g').charpoly := by
  classical
  obtain rfl := h.eq_reducedDegree
  let L := finiteGaloisSplittingField F D
  let e := finiteGaloisSplittingChart F D
  let gL := baseChange F L (reducedDegree F D) g
  let g'L := Units.map e.toMonoidHom
    (Units.map (Algebra.TensorProduct.includeRight : D →ₐ[F] L ⊗[F] D).toMonoidHom g')
  have hgL : gL.val.charpoly = g.val.charpoly.map (algebraMap F L) :=
    Matrix.charpoly_map _ _
  have hg'L : g'L.val.charpoly = (reducedCharpoly F D g'.val).map (algebraMap F L) :=
    (reducedCharpoly_map_chart F D e g'.val).symm
  have hchar : gL.val.charpoly = g'L.val.charpoly := by rw [hgL, hg'L, h.2.2]
  have hsq : Squarefree gL.val.charpoly := by
    rw [hgL]
    exact h.1.1.map.squarefree
  obtain ⟨q, hq⟩ := matrixConj_of_squarefree_charpoly_eq gL.val g'L.val hsq hchar
  let c := Langlands.GroupScheme.NormOneOuterDescent.conjugationAlgEquiv L q
  have hc : Units.map c.toMonoidHom gL = g'L := Units.ext hq
  have hgl : (adjointDefect g).charpoly.map (algebraMap F L) =
      (unitAdjointDefect L gL).charpoly := by
    have hmap : Units.map (matrixScalarChart L).toMonoidHom
        (Units.map (Algebra.TensorProduct.includeRight : _ →ₐ[F] L ⊗[F]
          Matrix (Fin (reducedDegree F D)) (Fin (reducedDegree F D)) F).toMonoidHom g) =
        gL := by
      apply Units.ext
      change (matrixEquivTensor (Fin (reducedDegree F D)) F L).symm (1 ⊗ₜ[F] g.val) = _
      rw [matrixEquivTensor_apply_symm, one_smul]
      rfl
    have he := charpoly_unitAdjointDefect_map F (matrixScalarChart L) g
    rw [hmap] at he
    exact he
  apply Polynomial.map_injective (algebraMap F L) (FaithfulSMul.algebraMap_injective F L)
  rw [hgl, charpoly_unitAdjointDefect_map F e g']
  change (unitAdjointDefect L gL).charpoly = (unitAdjointDefect L g'L).charpoly
  rw [← hc, ← unitAdjointDefect_conj L c, LinearEquiv.charpoly_conj]

/-- The adjoint discriminant on the division algebra is the coefficient at its
reduced degree in the characteristic polynomial of conjugation minus the identity. -/
def divisionWeylDiscriminant (g' : Dˣ) : F :=
  (unitAdjointDefect F g').charpoly.coeff (reducedDegree F D)

/-- The ordinary and division discriminants agree at matching regular elements. -/
theorem Corresponds.weylDiscriminant_eq {g : GeneralLinear n F} {g' : Dˣ}
    (h : Corresponds F D g g') :
    weylDiscriminant g = divisionWeylDiscriminant (F := F) g' := by
  change (adjointDefect g).charpoly.coeff n = _
  rw [h.adjointDefect_charpoly_eq, h.eq_reducedDegree]
  rfl

end Matching

end Langlands.JacquetLanglands
