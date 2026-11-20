import Langlands.Algebra.BrauerScalarExtension
import Langlands.Algebra.BrauerSplitting
import Langlands.Algebra.ReducedCharpoly
import Langlands.Algebra.ReducedNormFiniteChart

/-! # Reduced norm and reduced characteristic polynomials under field extension -/

noncomputable section

open Polynomial
open scoped TensorProduct

namespace Langlands.CentralSimple

universe u v

variable {K : Type u} [Field K] (A : CSA.{u, u} K)
  (E : Type u) [Field E] [Algebra K E]

/-- The norm law at an extension field is the reduced norm of the scalar-extended algebra. -/
theorem reducedNorm_baseChange (x : E ⊗[K] A) :
    reducedNorm E (Brauer.baseChange E A) E (1 ⊗ₜ[E] x) = reducedNorm K A E x := by
  let M := AlgebraicClosure E
  let e := (exists_matrix_chart_reducedDegree K A M).some
  let t := Brauer.baseChangeTowerEquiv E M A
  let e' : M ⊗[E] Brauer.baseChange E A ≃ₐ[M] Matrix _ _ M := t.trans e
  let f := Algebra.ofId E M
  apply (algebraMap E M).injective
  change f _ = (f.restrictScalars K) _
  erw [← reducedNorm_naturality E (Brauer.baseChange E A) f,
    ← reducedNorm_naturality K A (f.restrictScalars K),
    reducedNorm_eq_chart_det_fintype E (Brauer.baseChange E A) e',
    reducedNorm_eq_chart_det K A e]
  change (e (t _)).det = _
  apply congrArg (fun y => (e y).det)
  change t (1 ⊗ₜ[E] x) =
    Algebra.TensorProduct.map (f.restrictScalars K) (AlgHom.id K A) x
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    simp [t, f, Brauer.baseChangeTowerEquiv_tmul, Algebra.smul_def]
  | add x y hx hy =>
    simp only [TensorProduct.tmul_add, map_add, hx, hy]

/-- Every finite-index splitting chart computes the reduced characteristic polynomial. -/
theorem reducedCharpoly_map_chart_fintype {L : Type u} [Field L] [Algebra K L]
    {I : Type v} [Fintype I] [DecidableEq I] (e : L ⊗[K] A ≃ₐ[L] Matrix I I L) (a : A) :
    (reducedCharpoly K A a).map (algebraMap K L) = (e (1 ⊗ₜ[K] a)).charpoly := by
  rw [reducedCharpoly_map_chart K A (canonicalSizeChart K A e)]
  exact Matrix.charpoly_reindex _ _

/-- Extending the coefficients gives the reduced characteristic polynomial after base change. -/
theorem reducedCharpoly_baseChange (a : A) :
    reducedCharpoly E (Brauer.baseChange E A) (1 ⊗ₜ[K] a) =
      (reducedCharpoly K A a).map (algebraMap K E) := by
  let M := AlgebraicClosure E
  let e := (exists_matrix_chart_reducedDegree K A M).some
  let t := Brauer.baseChangeTowerEquiv E M A
  let e' : M ⊗[E] Brauer.baseChange E A ≃ₐ[M] Matrix _ _ M := t.trans e
  apply Polynomial.map_injective (algebraMap E M) (algebraMap E M).injective
  erw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq K E M,
    reducedCharpoly_map_chart_fintype (Brauer.baseChange E A) e',
    reducedCharpoly_map_chart K A e]
  change (e (t (1 ⊗ₜ[E] (1 ⊗ₜ[K] a)))).charpoly = _
  simp only [t, Brauer.baseChangeTowerEquiv_tmul, one_smul]

/-- A point over a field is invertible precisely when its reduced norm is nonzero. -/
theorem isUnit_iff_reducedNorm_ne_zero (x : E ⊗[K] A) :
    IsUnit x ↔ reducedNorm K A E x ≠ 0 := by
  refine ⟨fun h => (h.map (reducedNorm K A E)).ne_zero, fun h => ?_⟩
  refine (Algebra.lmul_isUnit_iff (R := E)).mp
    ((LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr ?_))
  change Algebra.norm E x ≠ 0
  rw [norm_eq_reducedNorm_pow K A E]
  exact pow_ne_zero _ h

/-- A matrix splitting chart makes every field unit a reduced norm. -/
theorem reducedNormUnits_surjective_of_split (h : Brauer.IsSplit (Brauer.baseChange E A)) :
    Function.Surjective (reducedNormUnits K A E) := by
  obtain ⟨n, hn, ⟨e'⟩⟩ := h
  let e : E ⊗[K] A ≃ₐ[E] Matrix (Fin n) (Fin n) E := e'
  let i : Fin n := ⟨0, hn⟩
  intro a
  let x := e.symm (Matrix.diagonal (fun j => if j = i then (a : E) else 1))
  have hx : reducedNorm K A E x = a := by
    rw [reducedNorm_eq_chart_det_fintype K A e]
    change (e (e.symm _)).det = _
    rw [AlgEquiv.apply_symm_apply, Matrix.det_diagonal]
    simp only [Finset.prod_ite_eq', Finset.mem_univ, ite_true]
  let hu := (isUnit_iff_reducedNorm_ne_zero A E x).mpr (hx ▸ a.ne_zero)
  exact ⟨hu.unit, Units.ext hx⟩

/-- Scalar extension preserves the reduced norm at field-valued points. -/
def ReducedNormScalarExtensionStatement : Prop :=
  ∀ (K E : Type u) [Field K] [Field E] [Algebra K E] (A : CSA.{u, u} K)
    (x : E ⊗[K] A), reducedNorm E (Brauer.baseChange E A) E (1 ⊗ₜ[E] x) =
      reducedNorm K A E x

/-- The reduced norm of the scalar-extended algebra is the original norm law at that field. -/
theorem reducedNormScalarExtension : ReducedNormScalarExtensionStatement.{u} := by
  intro K E _ _ _ A x
  exact reducedNorm_baseChange A E x

end Langlands.CentralSimple
