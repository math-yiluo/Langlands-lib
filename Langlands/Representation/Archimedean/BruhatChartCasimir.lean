import Langlands.Analysis.SliceChartDerivative
import Langlands.Analysis.SliceChartNeighborhood
import Langlands.Group.GL.BruhatCellMatrixSlice
import Langlands.Representation.Archimedean.BruhatWhittakerDirections

/-! # The transverse Casimir equation on a lower Bruhat chart -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

open Function Set Filter TopologicalSpace
open Langlands.Analysis Langlands.GeneralLinear Langlands.HarmonicAnalysis
open scoped ContDiff Distributions Matrix.Norms.Operator Topology

namespace Langlands.Archimedean

universe u uX uY

variable {F : Type u} [RCLike F] {r : ℕ}
  {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

local notation "M" => Matrix (Fin (r + 1)) (Fin (r + 1)) F
local notation "B" => upperTriangularSubgroup (r + 1) F
local notation "W" => (X × Y × ℝ)
local notation "D" => 𝓓(matrixUnitsOpen F (r + 1), ℂ)
local notation "DIdx" => (Fin (r + 1) × Bool)
local notation "RIdx" => (MatrixPositiveRoot (r + 1) × Bool)

private theorem single_diagonal_isUpperTriangular (i : Fin (r + 1)) (a : F) :
    (Matrix.single i i a).IsUpperTriangular := by
  intro j k hjk
  have h : ¬ (i = j ∧ i = k) := by
    rintro ⟨rfl, rfl⟩
    exact (lt_irrefl _ hjk)
  simp [Matrix.single, h]

private theorem transverseEquation_calculate (eigenvalue z d t s : ℂ)
    (h : eigenvalue * z = d + (2 * Complex.I) * (t + s)) :
    t = (2 * Complex.I)⁻¹ * (eigenvalue * z) - (2 * Complex.I)⁻¹ * d - s := by
  have hne : (2 * Complex.I : ℂ) ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  field_simp [hne]
  linear_combination -h

/-- The scalar Casimir equation gives an open vanishing neighborhood
of the center of the smooth Bruhat chart. -/
theorem matrixDistribution_bruhatChart_vanishing_neighborhood
    (w : Equiv.Perm (Fin (r + 1))) (a b : ℝ) (ψ : UnitaryAdditiveCharacter F)
    (hψ : ∀ z : F, ψ z = Circle.exp (a * RCLike.re z + b * RCLike.im z))
    (T : D →L[ℂ] ℂ) (eigenvalue : ℂ) (hCas : ∀ f : D, T (matrixTraceTestCasimir F (r + 1) f) = eigenvalue * T f)
    (hCov : ∀ (u : upperUnipotent (r + 1) F) (f : D),
      T (matrixLeftTranslateTest u.val f) = (Langlands.Whittaker.standardCharacter ψ r u : ℂ) * T f)
    (e : OpenPartialHomeomorph W M)
    (he : ContDiffOn ℝ ∞ e e.source) (hs : ContDiffOn ℝ ∞ e.symm e.target)
    (heΩ : e.target ⊆ matrixUnitsOpen F (r + 1))
    (hCell : ∀ z ∈ e.source, e z ∈ bruhatCellMatrixSet F w ↔ z.2 = 0)
    (hTang : ∀ (A : M), (∀ g : B, ∀ i j, bruhatNormalEntry w i j →
        ((g⁻¹ : B).val.val * A * g.val.val) i j = 0) →
      ∀ x : X, (x, 0) ∈ e.source →
        (chartVectorField e (fun z => A * z) (x, 0)).2 = 0)
    (hTrans : ∀ z ∈ e.source, fderiv ℝ e z (0, 0, 1) =
      (matrixWhittakerNormalPart (F := F) w a b).val * e z)
    (hT : Distribution.IsVanishingOn T (e.target \ bruhatCellMatrixSet F w))
    (he₀ : 0 ∈ e.source) :
    ∃ U : Set M, IsOpen U ∧ e 0 ∈ U ∧ U ⊆ e.target ∧ Distribution.IsVanishingOn T U := by
  classical
  apply exists_chart_vanishing_neighborhood e he hs he₀ heΩ T
  intro K₀ R hR hK
  let Ω : Opens W := ⟨e.source, e.open_source⟩
  let K := normalCoordinateBox K₀ R
  let L := complexDistributionRealTests (T.comp (smoothChartAmbientTest e hs))
  let P (f : 𝓓_{K}(W, ℝ)) : D :=
    smoothChartAmbientTest e hs (TestFunction.postcompCLM Complex.ofRealCLM
      (TestFunction.ofSupportedIn hK f))
  have hL : Distribution.IsVanishingOn L {p : W | p.2 ≠ 0} := by
    apply (isVanishingOn_complexDistributionRealTests_iff _ _).mpr
    refine isVanishingOn_smoothChartAmbientTest e hs heΩ T (fun z hz => ?_) hT
    exact ⟨e.map_source hz.1, fun h => hz.2 ((hCell z hz.1).mp h)⟩
  have hP (f : 𝓓_{K}(W, ℝ)) : (P f : M → ℂ) = transportCompactRealTest e hs hK f :=
    coe_smoothChartAmbientTest e hs heΩ _
  let tangent (A : M) : Prop := ∀ g : B, ∀ i j, bruhatNormalEntry w i j →
    ((g⁻¹ : B).val.val * A * g.val.val) i j = 0
  have hOps (A : M) (hA : tangent A) :
      ∃ op : 𝓓_{K}(W, ℝ) →ₗ[ℝ] 𝓓_{K}(W, ℝ),
        (∀ m (f : 𝓓_{K}(W, ℝ)), IsFlatOnZeroSlice m (f : W → ℝ) →
          IsFlatOnZeroSlice m (op f : W → ℝ)) ∧
        ∀ f : 𝓓_{K}(W, ℝ), P (op f) = matrixLeftTestDerivative A (P f) := by
    obtain ⟨op, hflat, h⟩ := exists_tangentChartDerivative e he hs hK (fun z : M => A * z)
      (contDiff_const.mul contDiff_id).contDiffOn (hTang A hA)
    refine ⟨op, hflat, fun f => TestFunction.ext fun y => ?_⟩
    change (P (op f) : M → ℂ) y = _
    rw [matrixLeftTestDerivative_apply, hP, hP]
    exact h f y
  choose op opFlat opEq using hOps
  let Z := matrixWhittakerLowerDirection F r a b
  let N := (matrixWhittakerNormalPart (F := F) w a b).val
  let A := Z - N
  have hA : tangent A := fun g i j h => upperConjugation_whittakerTangent_normalEntry_eq_zero w a b g h
  have hZ : matrixWhittakerLowerDirection F r a b = N + A := by
    change Z = N + A
    dsimp only [A]
    abel
  let E (d : DIdx) := matrixTraceUnit F (r + 1) (d.1, d.1, d.2)
  let E' (d : DIdx) := matrixTraceDualUnit F (r + 1) (d.1, d.1, d.2)
  let C (p : RIdx) :=
    let g := matrixTraceUnit F (r + 1) (p.1.val.1, p.1.val.2, p.2)
    let h := matrixTraceDualUnit F (r + 1) (p.1.val.1, p.1.val.2, p.2)
    g * h - h * g
  have hUpper (A : M) (h : A.IsUpperTriangular) : tangent A :=
    fun g _ _ hn => upperConjugation_normalEntry_eq_zero_of_upperTriangular w g A h hn
  have hE (d : DIdx) : tangent (E d) :=
    hUpper _ (single_diagonal_isUpperTriangular d.1 _)
  have hE' (d : DIdx) : tangent (E' d) :=
    hUpper _ (single_diagonal_isUpperTriangular d.1 _)
  have hC (p : RIdx) : tangent (C p) :=
    hUpper _ (fun _ _ h => matrixTraceUnit_mul_sub_dualUnit_isDiag (F := F)
      p.1.val.1 p.1.val.2 p.2 h.ne.symm)
  have hN (f : 𝓓_{K}(W, ℝ)) :
      P (compactTestLineDeriv (0, 0, 1) f) = matrixLeftTestDerivative N (P f) := by
    ext y
    change (P (compactTestLineDeriv (0, 0, 1) f) : M → ℂ) y = _
    rw [matrixLeftTestDerivative_apply, hP, hP]
    exact transportCompactRealTest_derivative e hs hK (fun z : M => N * z)
      (fun _ : W => (0, 0, 1))
      (fun z hz => (chartVectorField_eq_of_fderiv e he hs _ (hK hz) _ (hTrans z (hK hz))).symm)
      f _ (compactTestLineDeriv_apply (0, 0, 1) f) y
  let opD (d : DIdx) := (op (E d) (hE d)).comp (op (E' d) (hE' d))
  have hD (f : 𝓓_{K}(W, ℝ)) :
      T (matrixTraceDiagonalTestOperator F (r + 1) (P f)) =
        (∑ d : DIdx, T (P (opD d f))) + ∑ p : RIdx, T (P (op (C p) (hC p) f)) := by
    simp only [matrixTraceDiagonalTestOperator, add_apply, sum_apply,
      ContinuousLinearMap.comp_apply, map_add, map_sum, Fintype.sum_prod_type]
    simp only [opD, LinearMap.comp_apply, opEq, E, E', C]
  let I := Bool ⊕ (DIdx ⊕ RIdx)
  let V : I → 𝓓_{K}(W, ℝ) →ₗ[ℝ] 𝓓_{K}(W, ℝ) :=
    Sum.elim (fun k : Bool => if k then op A hA else LinearMap.id)
      (Sum.elim opD (fun p => op (C p) (hC p)))
  let c : ℂ := (2 * Complex.I)⁻¹
  let B₀ : I → ℂ →L[ℝ] ℂ :=
    Sum.elim (fun k : Bool => ContinuousLinearMap.mul ℝ ℂ (if k then -1 else c * eigenvalue))
      (fun _ => ContinuousLinearMap.mul ℝ ℂ (-c))
  have hFlat (i : I) (m : ℕ) (f : 𝓓_{K}(W, ℝ)) (hf : IsFlatOnZeroSlice m (f : W → ℝ)) :
      IsFlatOnZeroSlice m (V i f : W → ℝ) := by
    rcases i with k | d | p
    · cases k
      · exact hf
      · exact opFlat A hA m f hf
    · exact opFlat (E d) (hE d) m _ (opFlat (E' d) (hE' d) m f hf)
    · exact opFlat (C p) (hC p) m f hf
  have hEquation (f : 𝓓_{K}(W, ℝ)) :
      T (P (compactTestLineDeriv (0, 0, 1) f)) = ∑ i : I, B₀ i (T (P (V i f))) := by
    have h := matrixDistribution_traceCasimir_eq T ψ a b hψ hCov (P f)
    rw [hCas, hZ, matrixLeftTestDerivative_add, map_add, ← hN, ← opEq A hA] at h
    rw [transverseEquation_calculate _ _ _ _ _ h, hD]
    simp only [I, Fintype.sum_sum_type, Fintype.sum_bool, B₀, V, Sum.elim_inl, Sum.elim_inr,
      Bool.false_eq_true, ↓reduceIte, LinearMap.id_apply, ContinuousLinearMap.mul_apply',
      neg_one_mul, ← Finset.mul_sum]
    dsimp only [c]
    ring
  exact distribution_eq_zero_on_box_of_transverse_equation (Ω := Ω) L hL K₀ hR hK V B₀ hFlat hEquation

end Langlands.Archimedean
