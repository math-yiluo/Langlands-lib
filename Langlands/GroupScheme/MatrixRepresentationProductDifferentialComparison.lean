import Langlands.GroupScheme.MatrixRepresentationProductDifferentialComparisonStatement
import Langlands.GroupScheme.GeneralLinearProductCoordinateJet
import Langlands.GroupScheme.MatrixRepresentationProductOutputJet
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! # Equality of the actual analytic and dual-number product differentials -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Topology
open scoped Classical CategoryTheory.MonObj Matrix Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.MatrixRepresentation

open GeneralLinearProductDualNumber

variable {J : Type u} [Fintype J]
  {n : J → Type} [∀ j, Fintype (n j)] [∀ j, DecidableEq (n j)]
  {R : CommRingCat.{u}}
  {B : Type u} [NormedCommRing B] [NormedAlgebra ℝ B] [CompleteSpace B] [Algebra R B]
  {m : Type} [Fintype m] [DecidableEq m]

local instance comparisonFactorMatrixComplete (j : J) : CompleteSpace (Matrix (n j) (n j) B) :=
  inferInstanceAs (CompleteSpace (n j → n j → B))

private def matrixEntry {k : Type} [Fintype k] (i j : k) : Matrix k k B →L[ℝ] B where
  toLinearMap :=
    { toFun := fun A => A i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  cont := (continuous_apply j).comp (continuous_apply i)

omit [CompleteSpace B] in
private theorem hasDerivAt_entry {k : Type} [Fintype k]
    {f : ℝ → Matrix k k B} {Y : Matrix k k B} {t : ℝ}
    (h : HasDerivAt f Y t) (i j : k) :
    HasDerivAt (fun s => f s i j) (Y i j) t :=
  (matrixEntry (B := B) i j).hasFDerivAt.comp_hasDerivAt t h

private def identityCurve (X : ∀ j, Matrix (n j) (n j) B) (s : ℝ) : ∀ j, GL (n j) B :=
  (matrixUnitsChart (n := n) (B := B)).symm (1 + s • X)

private theorem identityCurve_zero (X : ∀ j, Matrix (n j) (n j) B) :
    identityCurve X 0 = 1 := by
  simp only [identityCurve, zero_smul, add_zero, matrixUnitsChart]
  exact IsOpenEmbedding.toOpenPartialHomeomorph_left_inv _
    (isOpenEmbedding_matrixValues (n := n) (B := B)) (x := (1 : ∀ j, GL (n j) B))

omit [CompleteSpace B] in
private theorem line_hasDerivAt (X : ∀ j, Matrix (n j) (n j) B) :
    HasDerivAt (fun s : ℝ => 1 + s • X) X 0 := by
  convert! ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add 1 using 1
  simp only [one_smul]

private theorem identityCurve_values (X : ∀ j, Matrix (n j) (n j) B) :
    (fun s => fun j => (identityCurve X s j : Matrix (n j) (n j) B)) =ᶠ[𝓝 0]
      (fun s : ℝ => 1 + s • X) := by
  have h := (line_hasDerivAt X).continuousAt
  have hmem := h.preimage_mem_nhds
    (isOpenEmbedding_matrixValues.isOpen_range.mem_nhds
      (show (1 + (0 : ℝ) • X) ∈ Set.range
        (fun g : ∀ j, GL (n j) B => fun j => (g j : Matrix (n j) (n j) B)) by
          simpa only [zero_smul, add_zero] using
            (show (1 : ∀ j, Matrix (n j) (n j) B) ∈ Set.range
              (fun g : ∀ j, GL (n j) B => fun j => (g j : Matrix (n j) (n j) B))
              from ⟨1, rfl⟩)))
  filter_upwards [hmem] with s hs
  exact IsOpenEmbedding.toOpenPartialHomeomorph_right_inv _
    (isOpenEmbedding_matrixValues (n := n) (B := B)) hs

private theorem identityCurve_hasDerivAt (X : ∀ j, Matrix (n j) (n j) B) (j : J) :
    HasDerivAt (fun s => (identityCurve X s j : Matrix (n j) (n j) B)) (X j) 0 := by
  have h := (line_hasDerivAt X).congr_of_eventuallyEq (identityCurve_values X)
  exact (ContinuousLinearMap.proj j).hasFDerivAt.comp_hasDerivAt 0 h

private theorem identityCurve_inv_hasDerivAt (X : ∀ j, Matrix (n j) (n j) B) (j : J) :
    HasDerivAt (fun s => ((identityCurve X s j)⁻¹ : GL (n j) B).val) (-X j) 0 := by
  have h := (hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : GL (n j) B)).comp_hasDerivAt_of_eq 0
    (identityCurve_hasDerivAt X j) (by simp [identityCurve_zero])
  simpa only [Function.comp_def, Ring.inverse_unit, neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, inv_one, Units.val_one, one_mul, mul_one] using h

private theorem identityCurve_coordinateJet (X : ∀ j, Matrix (n j) (n j) B) :
    (groupScheme n R).CoordinateJet
      (fun s => (affineMatrixEquiv (n := n) (R := R) B).symm (identityCurve X s))
      (pointUnit X) 0 := by
  rw [← affineMatrixEquiv_symm_matrixUnit X]
  apply coordinateJet_affineMatrixEquiv_symm
  intro j c
  cases c with
  | entry a b =>
      constructor
      · by_cases hab : a = b <;>
          simp [GeneralLinear.values, identityCurve_zero, GeneralLinear.DualNumber.matrixUnit,
            hab]
      · by_cases hab : a = b <;>
          simpa [GeneralLinear.values, GeneralLinear.DualNumber.matrixUnit, Matrix.one_apply, hab]
            using hasDerivAt_entry (identityCurve_hasDerivAt X j) a b
  | inverseEntry a b =>
      change ((1 - GeneralLinear.DualNumber.epsilonMatrix (X j) :
        Matrix (n j) (n j) (DualNumber B)) a b).fst =
          ((identityCurve X 0 j)⁻¹ : GL (n j) B).val a b ∧
        HasDerivAt (fun s => ((identityCurve X s j)⁻¹ : GL (n j) B).val a b)
          ((1 - GeneralLinear.DualNumber.epsilonMatrix (X j) :
            Matrix (n j) (n j) (DualNumber B)) a b).snd 0
      constructor
      · by_cases hab : a = b <;> simp [identityCurve_zero, hab]
      · by_cases hab : a = b <;> simpa [Matrix.one_apply, hab] using
          hasDerivAt_entry (identityCurve_inv_hasDerivAt X j) a b

private theorem hasDerivAt_analytic_along_curve
    (ρ : MatrixRepresentation (groupScheme n R) m) (X : ∀ j, Matrix (n j) (n j) B) :
    HasDerivAt (fun s => (ρ.productMatrixPointsHom B (identityCurve X s) : Matrix m m B))
      (ρ.analyticProductDifferential (B := B) X) 0 := by
  have h := (ρ.hasFDerivAt_analyticProductDifferential (B := B)).comp_hasDerivAt_of_eq 0
    (line_hasDerivAt X) (by simp only [zero_smul, add_zero])
  apply h.congr_of_eventuallyEq
  filter_upwards [identityCurve_values X] with s hs
  have hh := ρ.productMatrixCoordinateExtension_apply (identityCurve X s)
  rw [hs] at hh
  exact hh.symm

/-- The actual Frechet derivative and the independently constructed algebraic
product differential agree for every genuine representation in the full scope
of the published target. -/
theorem analyticProductDifferentialComparison
    (ρ : MatrixRepresentation (groupScheme n R) m) :
    AnalyticProductDifferentialComparison (B := B) ρ := by
  intro X
  apply Matrix.ext
  intro i j
  have ha := hasDerivAt_entry (hasDerivAt_analytic_along_curve ρ X) i j
  have hd := hasDerivAt_productMatrixPointsHom_of_coordinateJet ρ
    (identityCurve X) X 0 (identityCurve_coordinateJet (R := R) X) i j
  exact ha.unique hd

end Langlands.GroupScheme.MatrixRepresentation
