import Langlands.AlgebraicGeometry.PointManifold.General.RegularEvaluation
import Langlands.AlgebraicGeometry.PointManifold.RegularCharts
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! # Universe-general regular charts on the existing affine point topology -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open scoped Manifold ContDiff

namespace Langlands.AlgebraicGeometry.PointManifold.General

open PointTopology

variable (k : Type u) [RCLike k]
variable (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left] (d : ℕ)

/-- Local analytic output, to be constructed from algebraic smoothness.
The chart is a partial homeomorphism for the already published evaluation topology. -/
structure RegularChart where
  homeomorph : OpenPartialHomeomorph (RingPoint k X k) (Fin d → k)
  numerator : Fin d → AffineCoordinateRing k X
  denominator : Fin d → AffineCoordinateRing k X
  denominator_ne_zero : ∀ p ∈ homeomorph.source, ∀ i,
    regularEvaluation p (denominator i) ≠ 0
  apply_eq : ∀ p ∈ homeomorph.source, ∀ i,
    homeomorph p i =
      regularEvaluation p (numerator i) / regularEvaluation p (denominator i)
  contDiffOn_inverse_evaluation : ∀ a : AffineCoordinateRing k X,
    ContDiffOn ℝ ∞ (fun v => regularEvaluation (homeomorph.symm v) a) homeomorph.target

/-- A covering family of regular charts, without an algebraic smoothness assumption. -/
structure RegularAtlas where
  chartAt : RingPoint k X k → RegularChart k X d
  mem_source : ∀ p, p ∈ (chartAt p).homeomorph.source

namespace RegularAtlas

variable {k X d}

/-- The charted space uses the existing actual point carrier and evaluation topology. -/
@[instance_reducible] def chartedSpace (A : RegularAtlas k X d) :
    ChartedSpace (Fin d → k) (RingPoint k X k) where
  atlas := Set.range (fun p => (A.chartAt p).homeomorph)
  chartAt p := (A.chartAt p).homeomorph
  mem_chart_source := A.mem_source
  chart_mem_atlas p := ⟨p, rfl⟩

/-- Empty point spaces have a covering regular atlas, in every dimension. -/
def ofIsEmpty [IsEmpty (RingPoint k X k)] : RegularAtlas k X d where
  chartAt p := isEmptyElim p
  mem_source p := isEmptyElim p

end RegularAtlas

theorem model_finrank :
    Module.finrank ℝ (Fin d → k) = d * Module.finrank ℝ k := by
  simp [Module.finrank_pi_fintype]

theorem real_model_finrank (d : ℕ) : Module.finrank ℝ (Fin d → ℝ) = d := by
  simp

theorem complex_model_finrank (d : ℕ) : Module.finrank ℝ (Fin d → ℂ) = 2 * d := by
  simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, Nat.mul_comm]

section TypeZero

variable {k : Type} [RCLike k]
  {X : Over (Spec (CommRingCat.of k))} [IsAffine X.left] {d : ℕ}

/-- The two chart interfaces have exactly the same data at Type 0. -/
def RegularChart.typeZeroEquiv : PointManifold.RegularChart k X d ≃ RegularChart k X d where
  toFun c := ⟨c.homeomorph, c.numerator, c.denominator, c.denominator_ne_zero,
    c.apply_eq, c.contDiffOn_inverse_evaluation⟩
  invFun c := ⟨c.homeomorph, c.numerator, c.denominator, c.denominator_ne_zero,
    c.apply_eq, c.contDiffOn_inverse_evaluation⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem RegularChart.typeZeroEquiv_homeomorph (c : PointManifold.RegularChart k X d) :
    (RegularChart.typeZeroEquiv c).homeomorph = c.homeomorph := rfl

@[simp] theorem RegularChart.typeZeroEquiv_symm_homeomorph (c : RegularChart k X d) :
    (RegularChart.typeZeroEquiv.symm c).homeomorph = c.homeomorph := rfl

/-- Atlas conversion preserves every chosen partial homeomorphism. -/
def RegularAtlas.typeZeroEquiv : PointManifold.RegularAtlas k X d ≃ RegularAtlas k X d where
  toFun A := ⟨fun p => RegularChart.typeZeroEquiv (A.chartAt p), A.mem_source⟩
  invFun A := ⟨fun p => RegularChart.typeZeroEquiv.symm (A.chartAt p), A.mem_source⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Conversion preserves the exact charted-space structure, with its existing topology. -/
@[simp] theorem RegularAtlas.typeZeroEquiv_chartedSpace (A : PointManifold.RegularAtlas k X d) :
    (RegularAtlas.typeZeroEquiv A).chartedSpace = A.chartedSpace := rfl

@[simp] theorem RegularAtlas.typeZeroEquiv_symm_chartedSpace (A : RegularAtlas k X d) :
    (RegularAtlas.typeZeroEquiv.symm A).chartedSpace = A.chartedSpace := rfl

end TypeZero

end Langlands.AlgebraicGeometry.PointManifold.General
