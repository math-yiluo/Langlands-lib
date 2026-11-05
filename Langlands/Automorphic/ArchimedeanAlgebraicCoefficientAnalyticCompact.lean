import Langlands.Automorphic.ArchimedeanAlgebraicCoefficientAnalyticCovariance
import Langlands.Automorphic.CochainCompactDifferentiation
import Langlands.Global.ArchimedeanCochainInsertion

/-! # Actual compact differentiation and insertion for analytic coefficients -/

noncomputable section

universe uF

open scoped Classical TensorProduct Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.ArchimedeanAlgebraicCoefficient

open Langlands.Global Langlands.Global.ArchimedeanGL Langlands.GroupScheme

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}
variable {I : Type} [Fintype I] (e : I → EmbeddingIndex F)
variable {m : Type} [Fintype m] [DecidableEq m]
variable (ρ : MatrixRepresentation
  (GeneralLinearProductDualNumber.groupScheme (fun _ : I => Fin n)
    (CommRingCat.of ℂ)) m)

/-- Differentiating the original coefficient action along an actual compact
curve gives its constructed analytic Lie action. -/
theorem analyticCompactCurve_deriv
    (X : RealLieAlgebra F n) (c : ℝ → standardInfiniteCompact F n)
    (hc0 : c 0 = 1)
    (hc : HasDerivAt
      (fun t : ℝ => (archimedeanGLCoordinates F n (c t).val : ArchimedeanMatrix F n))
      (realLieAlgebraToMatrix F n X) 0)
    (v : AnalyticSpace e ρ) :
    HasDerivAt (fun t => analyticCompactRepresentation e ρ (c t) v)
      ⁅complexify F n X, v⁆ 0 := by
  change HasDerivAt
    (fun t => representation e ρ (c t).val (analyticCoordinates e ρ v))
    (analyticComplexDifferential e ρ (complexify F n X) (analyticCoordinates e ρ v)) 0
  rw [complexify_apply, analyticComplexDifferential_tmul, one_smul]
  have h0 : (1 : ArchimedeanMatrix F n) =
      (archimedeanGLCoordinates F n (c 0).val : ArchimedeanMatrix F n) := by
    simp [hc0]
  have hd : HasDerivAt
      (fun t : ℝ => orbitCoordinateExtension e ρ (analyticCoordinates e ρ v)
        (archimedeanGLCoordinates F n (c t).val : ArchimedeanMatrix F n))
      (orbitDerivative e ρ (analyticCoordinates e ρ v) (realLieAlgebraToMatrix F n X)) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (𝕜 := ℝ)
      (F := ArchimedeanMatrix F n) (E := Space e ρ)
      (l := orbitCoordinateExtension e ρ (analyticCoordinates e ρ v))
      (l' := orbitDerivative e ρ (analyticCoordinates e ρ v))
      (f := fun t : ℝ =>
        (archimedeanGLCoordinates F n (c t).val : ArchimedeanMatrix F n))
      (f' := realLieAlgebraToMatrix F n X) (y := 1) (0 : ℝ)
      (hasFDerivAt_orbitCoordinateExtension e ρ (analyticCoordinates e ρ v)) hc h0
  rw [orbitDerivative_realLie] at hd
  convert hd using 1
  funext t
  exact (orbitCoordinateExtension_apply e ρ (analyticCoordinates e ρ v) (c t).val).symm

private def analyticCoordinateEvaluation (i : m) : AnalyticSpace e ρ →ₗ[ℂ] ℂ :=
  (LinearMap.proj i).comp ((coordinates e ρ).toLinearMap.comp
    (analyticCoordinates e ρ).toLinearMap)

/-- Genuine coefficient differentiation proves compact insertion first on
tuples of real Lie directions. -/
theorem analyticCochain_compact_real (q : ℕ)
    (f : (ComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ] AnalyticSpace e ρ)
    (hf : f ∈ HorizontalAlternating.equivariant
      (complexCompactRepresentation F n) (analyticCompactRepresentation e ρ) q)
    (Y : compactLieSubalgebra F n) (X : Fin q → RealLieAlgebra F n) :
    ⁅complexify F n Y.val, f (fun i => complexify F n (X i))⁆ =
      ∑ i, f (Function.update (fun j => complexify F n (X j)) i
        (complexify F n ⁅Y.val, X i⁆)) := by
  obtain ⟨c, hc0, hc⟩ := compactTangentCurve F n Y
  apply (analyticCoordinates e ρ).injective
  apply (coordinates e ρ).injective
  funext i
  let ℓ := analyticCoordinateEvaluation e ρ i
  have hd := ((ℓ.toContinuousLinearMap).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (analyticCompactCurve_deriv e ρ Y.val c hc0 hc
      (f (fun j => complexify F n (X j))))
  have he := compactCurve_scalarCochain_deriv F n q f ℓ Y X c hc0 hc
  have hcurve :
      (fun t => ℓ (f (fun j => complexify F n
        (realLieConjugation F n (c t).val (X j))))) =
      (fun t => ℓ (analyticCompactRepresentation e ρ (c t)
        (f (fun j => complexify F n (X j))))) := by
    funext t
    have hh := hf (c t) (fun j => complexify F n (X j))
    simpa only [complexCompactRepresentation_apply,
      complexLieConjugation_complexify] using congrArg ℓ hh
  rw [hcurve] at he
  have hu := hd.unique he
  rw [← map_sum] at hu
  exact hu

/-- The real compact insertion identity holds on all complex input tuples. -/
theorem analyticCochain_compact_real_complex (q : ℕ)
    (f : (ComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ] AnalyticSpace e ρ)
    (hf : f ∈ HorizontalAlternating.equivariant
      (complexCompactRepresentation F n) (analyticCompactRepresentation e ρ) q)
    (Y : compactLieSubalgebra F n) (X : Fin q → ComplexLieAlgebra F n) :
    ⁅complexify F n Y.val, f X⁆ =
      ∑ i, f (Function.update X i ⁅complexify F n Y.val, X i⁆) :=
  complexCochainInsertion_of_real F n q f
    (analyticComplexLieAction e ρ (complexify F n Y.val)) Y.val
    (analyticCochain_compact_real e ρ q f hf Y) X

/-- Actual full compact equivariance implies the complex compact insertion
identity on the entire genuinely differentiated coefficient carrier. -/
theorem analyticCochain_compact_complex (q : ℕ)
    (f : (ComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ] AnalyticSpace e ρ)
    (hf : f ∈ HorizontalAlternating.equivariant
      (complexCompactRepresentation F n) (analyticCompactRepresentation e ρ) q)
    (Y : CompactComplexLieAlgebra F n) (X : Fin q → ComplexLieAlgebra F n) :
    analyticCompactLieAction e ρ Y (f X) =
      ∑ i, f (Function.update X i ⁅compactComplexInclusion F n Y, X i⁆) := by
  induction Y using TensorProduct.inductionOn with
  | tmul z Y =>
    change analyticComplexLieAction e ρ (compactComplexInclusion F n (z ⊗ₜ[ℝ] Y))
      (f X) = _
    rw [compactComplexInclusion_tmul]
    have ht : z ⊗ₜ[ℝ] Y.val = z • complexify F n Y.val := by
      simp only [complexify_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [ht, map_smul, LinearMap.smul_apply]
    change z • ⁅complexify F n Y.val, f X⁆ = _
    rw [analyticCochain_compact_real_complex e ρ q f hf Y X, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [_root_.smul_lie z (complexify F n Y.val) (X i)]
    exact (f.map_update_smul X i z ⁅complexify F n Y.val, X i⁆).symm
  | add Y Z hY hZ =>
    simp only [map_add, LinearMap.add_apply, add_lie, f.map_update_add,
      Finset.sum_add_distrib, hY, hZ]

/-- Actual coefficient cochains satisfying the compact insertion identity. -/
def analyticInfinitesimalCompactCochains (q : ℕ) :
    Submodule ℂ ((ComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ] AnalyticSpace e ρ) where
  carrier := {f | ∀ (Y : CompactComplexLieAlgebra F n) (X : Fin q → ComplexLieAlgebra F n),
    analyticCompactLieAction e ρ Y (f X) =
      ∑ i, f (Function.update X i ⁅compactComplexInclusion F n Y, X i⁆)}
  zero_mem' := by intro Y X; simp
  add_mem' hf hg := by
    intro Y X
    simpa only [AlternatingMap.add_apply, map_add, Finset.sum_add_distrib] using
      congrArg₂ (· + ·) (hf Y X) (hg Y X)
  smul_mem' z f hf := by
    intro Y X
    simpa only [AlternatingMap.smul_apply, map_smul, Finset.smul_sum] using
      congrArg (fun v : AnalyticSpace e ρ => z • v) (hf Y X)

/-- Identity on coefficient cochains, with infinitesimal membership derived
by actual differentiation of full compact equivariance. -/
def analyticCompactEquivariantLieInclusion (q : ℕ) :
    HorizontalAlternating.equivariant
      (complexCompactRepresentation F n) (analyticCompactRepresentation e ρ) q →ₗ[ℂ]
        analyticInfinitesimalCompactCochains e ρ q where
  toFun f := ⟨f.val, analyticCochain_compact_complex e ρ q f.val f.property⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

@[simp]
theorem analyticCompactEquivariantLieInclusion_coe (q : ℕ)
    (f : HorizontalAlternating.equivariant
      (complexCompactRepresentation F n) (analyticCompactRepresentation e ρ) q) :
    (analyticCompactEquivariantLieInclusion e ρ q f).val = f.val := rfl

theorem analyticCompactEquivariantLieInclusion_injective (q : ℕ) :
    Function.Injective (analyticCompactEquivariantLieInclusion e ρ q) := by
  intro f g h
  exact Subtype.ext (congrArg
    (fun v : analyticInfinitesimalCompactCochains e ρ q => v.val) h)

end Langlands.Automorphic.ArchimedeanAlgebraicCoefficient
