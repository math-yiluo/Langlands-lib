import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.RingTheory.MatrixPolynomialAlgebra
import Mathlib.Topology.Instances.Matrix

/-!
# The invertible complex matrices form a connected set

`isPreconnected_complexMatrixUnits` proves that the set of invertible `n × n` complex matrices
is preconnected, and `isConnected_complexMatrixUnits` that it is connected. The Prop-valued
statement `ComplexMatrixUnitsPreconnectedStatement` packages the first assertion for every `n`.
See the paired Markdown.
-/

namespace Langlands.Global.RankinSelbergGlobal

open Polynomial

/-- The invertible `n × n` complex matrices form a preconnected subset of the space of all
`n × n` complex matrices, for every `n`. -/
def ComplexMatrixUnitsPreconnectedStatement : Prop :=
  ∀ n : ℕ, IsPreconnected {X : Matrix (Fin n) (Fin n) ℂ | IsUnit X}

/-- The determinant of `X + t • (Y - X)` as a polynomial in `t`. -/
noncomputable def complexMatrixSegmentDetPoly {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) : ℂ[X] :=
  Matrix.det (X.map C + (Polynomial.X : ℂ[X]) • (Y - X).map C)

theorem eval_complexMatrixSegmentDetPoly {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) (t : ℂ) :
    (complexMatrixSegmentDetPoly X Y).eval t = Matrix.det (X + t • (Y - X)) := by
  rw [complexMatrixSegmentDetPoly, ← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp [RingHom.mapMatrix_apply]

theorem complexMatrixSegmentDetPoly_ne_zero {n : ℕ} {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : IsUnit X) (Y : Matrix (Fin n) (Fin n) ℂ) : complexMatrixSegmentDetPoly X Y ≠ 0 := by
  intro h
  have h0 := eval_complexMatrixSegmentDetPoly X Y 0
  rw [h, eval_zero, zero_smul, add_zero] at h0
  exact ((Matrix.isUnit_iff_isUnit_det X).1 hX).ne_zero h0.symm

/-- **The invertible complex matrices form a preconnected set.** Two invertible matrices `X` and
`Y` are joined inside the invertible matrices by the image of the complement of the finite zero
set of the polynomial `t ↦ det (X + t • (Y - X))`. -/
theorem isPreconnected_complexMatrixUnits (n : ℕ) :
    IsPreconnected {X : Matrix (Fin n) (Fin n) ℂ | IsUnit X} := by
  refine isPreconnected_of_forall_pair fun X hX Y _ => ?_
  set p := complexMatrixSegmentDetPoly X Y
  have hp : p ≠ 0 := complexMatrixSegmentDetPoly_ne_zero hX Y
  have hfin : {t : ℂ | p.IsRoot t}.Finite := Polynomial.finite_setOfPred_isRoot hp
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    exact Nat.one_lt_ofNat
  have hconn : IsPathConnected {t : ℂ | p.IsRoot t}ᶜ :=
    hfin.countable.isPathConnected_compl_of_one_lt_rank hrank
  let f : ℂ → Matrix (Fin n) (Fin n) ℂ := fun t => X + t • (Y - X)
  have hf : Continuous f := continuous_const.add (continuous_id.smul continuous_const)
  refine ⟨f '' {t : ℂ | p.IsRoot t}ᶜ, ?_, ⟨0, ?_, ?_⟩, ⟨1, ?_, ?_⟩,
    hconn.isConnected.isPreconnected.image f hf.continuousOn⟩
  · rintro _ ⟨t, ht, rfl⟩
    refine (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 ?_)
    rw [← eval_complexMatrixSegmentDetPoly]
    exact ht
  · show ¬ p.IsRoot 0
    rw [Polynomial.IsRoot, eval_complexMatrixSegmentDetPoly, zero_smul, add_zero]
    exact ((Matrix.isUnit_iff_isUnit_det X).1 hX).ne_zero
  · simp [f]
  · show ¬ p.IsRoot 1
    rw [Polynomial.IsRoot, eval_complexMatrixSegmentDetPoly, one_smul, add_sub_cancel]
    exact ((Matrix.isUnit_iff_isUnit_det Y).1 ‹_›).ne_zero
  · simp [f]

/-- The invertible complex matrices form a connected set. -/
theorem isConnected_complexMatrixUnits (n : ℕ) :
    IsConnected {X : Matrix (Fin n) (Fin n) ℂ | IsUnit X} :=
  ⟨⟨1, isUnit_one⟩, isPreconnected_complexMatrixUnits n⟩

/-- Proof of `ComplexMatrixUnitsPreconnectedStatement`. -/
theorem complexMatrixUnitsPreconnected : ComplexMatrixUnitsPreconnectedStatement :=
  isPreconnected_complexMatrixUnits

end Langlands.Global.RankinSelbergGlobal
