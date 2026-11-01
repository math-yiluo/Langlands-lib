import Langlands.Global.ArchimedeanAdjointCoefficientsStatement
import Langlands.Global.ArchimedeanSmoothTopology
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin

/-! # Finite smooth coefficients for actual enveloping conjugation -/

noncomputable section

universe u v

open scoped Classical BigOperators TensorProduct Matrix.Norms.Operator Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Constant actual smooth functions. -/
def smoothFunctionConst (z : ℂ) : SmoothFunctions K n :=
  ⟨fun _ => z, contMDiff_const⟩

/-- Pointwise multiplication of actual smooth functions. -/
def smoothFunctionMul (f h : SmoothFunctions K n) : SmoothFunctions K n :=
  ⟨fun g => f.val g * h.val g, by
    exact (show ContDiff ℝ ∞ (fun p : ℂ × ℂ => p.1 * p.2) from
      contDiff_fst.mul contDiff_snd).contMDiff.comp
        (f.property.prodMk_space h.property)⟩

/-- Inversion pullback of an actual smooth function. -/
def smoothFunctionInv (f : SmoothFunctions K n) : SmoothFunctions K n :=
  ⟨fun g => f.val g⁻¹, by
    change ContMDiff 𝓘(ℝ, ArchimedeanMatrix K n) 𝓘(ℝ, ℂ) ∞ _
    simpa only [Function.comp_def, map_inv] using f.property.comp
      (contMDiff_inv _ _ : ContMDiff 𝓘(ℝ, ArchimedeanMatrix K n)
        𝓘(ℝ, ArchimedeanMatrix K n) ∞ (fun g : ArchimedeanGL K n => g⁻¹))⟩

private def HasFiniteSmoothCoefficients (a : EnvelopingAlgebra K n) : Prop :=
  ∃ m : ℕ, ∃ b : Fin m → EnvelopingAlgebra K n,
    ∃ c : Fin m → SmoothFunctions K n,
      ∀ g, envelopingConjugation K n g a = ∑ i, ((c i).val g) • b i

private theorem coefficients_of_fintype
    {ι : Type v} [Fintype ι] (a : EnvelopingAlgebra K n)
    (b : ι → EnvelopingAlgebra K n) (c : ι → SmoothFunctions K n)
    (h : ∀ g, envelopingConjugation K n g a = ∑ i, ((c i).val g) • b i) :
    HasFiniteSmoothCoefficients K n a := by
  classical
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, b ∘ e.symm, c ∘ e.symm, ?_⟩
  intro g
  rw [h g]
  exact (e.symm.sum_comp (fun i => ((c i).val g) • b i)).symm

private theorem coefficients_scalar (z : ℂ) :
    HasFiniteSmoothCoefficients K n (algebraMap ℂ (EnvelopingAlgebra K n) z) := by
  refine ⟨1, fun _ => 1, fun _ => smoothFunctionConst K n z, ?_⟩
  intro g
  simp [Algebra.algebraMap_eq_smul_one, smoothFunctionConst]

private theorem coefficients_add (a d : EnvelopingAlgebra K n)
    (ha : HasFiniteSmoothCoefficients K n a) (hd : HasFiniteSmoothCoefficients K n d) :
    HasFiniteSmoothCoefficients K n (a + d) := by
  classical
  obtain ⟨m, b, c, hc⟩ := ha
  obtain ⟨l, e, f, hf⟩ := hd
  apply coefficients_of_fintype K n (a + d) (Sum.elim b e) (Sum.elim c f)
  intro g
  simp only [map_add, hc, hf, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

private theorem coefficients_mul (a d : EnvelopingAlgebra K n)
    (ha : HasFiniteSmoothCoefficients K n a) (hd : HasFiniteSmoothCoefficients K n d) :
    HasFiniteSmoothCoefficients K n (a * d) := by
  classical
  obtain ⟨m, b, c, hc⟩ := ha
  obtain ⟨l, e, f, hf⟩ := hd
  apply coefficients_of_fintype K n (a * d)
    (fun i : Fin m × Fin l => b i.1 * e i.2)
    (fun i : Fin m × Fin l => smoothFunctionMul K n (c i.1) (f i.2))
  intro g
  simp only [map_mul, hc, hf, Fintype.sum_prod_type, smoothFunctionMul,
    Finset.sum_mul, Finset.mul_sum, smul_mul_smul]
  exact Finset.sum_comm

private theorem coefficients_smul (z : ℂ) (a : EnvelopingAlgebra K n)
    (ha : HasFiniteSmoothCoefficients K n a) :
    HasFiniteSmoothCoefficients K n (z • a) := by
  obtain ⟨m, b, c, hc⟩ := ha
  refine ⟨m, b, fun i => smoothFunctionMul K n (smoothFunctionConst K n z) (c i), ?_⟩
  intro g
  simp only [map_smul, hc, Finset.smul_sum, smul_smul,
    smoothFunctionMul, smoothFunctionConst]


private theorem contDiff_algebra_conjugation_product
    {R : Type v} [NormedRing R] [NormedAlgebra ℝ R] (X : R) :
    ContDiff ℝ ∞ (fun p : R × R => p.1 * X * p.2) :=
  (contDiff_fst.mul contDiff_const).mul contDiff_snd

private theorem contMDiff_algebra_conjugation
    {R : Type v} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R] (X : R) :
    ContMDiff 𝓘(ℝ, R) 𝓘(ℝ, R) ∞
      (fun g : Rˣ => (g : R) * X * (g⁻¹ : Rˣ).val) := by
  have hval : ContMDiff 𝓘(ℝ, R) 𝓘(ℝ, R) ∞ (fun g : Rˣ => (g : R)) :=
    Units.contMDiff_val
  have hinv : ContMDiff 𝓘(ℝ, R) 𝓘(ℝ, R) ∞
      (fun g : Rˣ => (g⁻¹ : Rˣ).val) :=
    hval.comp (contMDiff_inv _ _)
  exact (contDiff_algebra_conjugation_product X).contMDiff.comp
    (hval.prodMk_space hinv)

/-- A continuous real linear coordinate of matrix conjugation is an actual
smooth scalar function. -/
def smoothConjugationCoordinate (X : ArchimedeanMatrix K n)
    (L : ArchimedeanMatrix K n →L[ℝ] ℂ) : SmoothFunctions K n :=
  ⟨fun g => L ((archimedeanGLCoordinates K n g).val * X *
      (archimedeanGLCoordinates K n g⁻¹).val), by
    change ContMDiff 𝓘(ℝ, ArchimedeanMatrix K n) 𝓘(ℝ, ℂ) ∞ _
    have h := L.contDiff.contMDiff.comp (contMDiff_algebra_conjugation X)
    simpa only [Function.comp_def, map_inv, ContinuousMulEquiv.apply_symm_apply] using h⟩

private theorem coefficients_real_generator (X : RealLieAlgebra K n) :
    HasFiniteSmoothCoefficients K n (envelopingGenerator K n (complexify K n X)) := by
  classical
  let B := Module.finBasis ℝ (ArchimedeanMatrix K n)
  let T : ArchimedeanMatrix K n →ₗ[ℝ] EnvelopingAlgebra K n :=
    ((envelopingGenerator K n).toLinearMap.restrictScalars ℝ).comp
      ((complexify K n).toLinearMap.comp (realLieAlgebraToMatrix K n).symm.toLinearMap)
  let Y : InfiniteAdelicGL K n → ArchimedeanMatrix K n := fun g =>
    (archimedeanGLCoordinates K n g).val * realLieAlgebraToMatrix K n X *
      (archimedeanGLCoordinates K n g⁻¹).val
  let c : Fin (Module.finrank ℝ (ArchimedeanMatrix K n)) →
      SmoothFunctions K n := fun i => smoothConjugationCoordinate K n
        (realLieAlgebraToMatrix K n X)
        (Complex.ofRealCLM.comp (B.coord i).toContinuousLinearMap)
  refine ⟨_, fun i => T (B i), c, ?_⟩
  intro g
  have hgen :
      envelopingConjugation K n g (envelopingGenerator K n (complexify K n X)) =
        T (Y g) := by
    rw [envelopingConjugation_generator, complexLieConjugation_complexify,
      realLieConjugation_apply]
    rfl
  rw [hgen, ← B.sum_repr (Y g)]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  exact (IsScalarTower.algebraMap_smul ℂ (B.repr (Y g) i) (T (B i))).symm

private theorem coefficients_complex_generator (X : ComplexLieAlgebra K n) :
    HasFiniteSmoothCoefficients K n (envelopingGenerator K n X) := by
  induction X using TensorProduct.inductionOn with
  | tmul z X =>
    have h : z ⊗ₜ[ℝ] X = z • complexify K n X := by
      simp only [complexify_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h, map_smul]
    exact coefficients_smul K n z _ (coefficients_real_generator K n X)
  | add X Y hX hY =>
    rw [map_add]
    exact coefficients_add K n _ _ hX hY

/-- Every actual enveloping element has a finite, globally smooth expansion
of all its conjugates in a fixed family of enveloping elements. -/
theorem envelopingConjugationSmoothCoefficients
    (K : Type u) [Field K] [NumberField K] (n : ℕ) :
    ∀ a : EnvelopingAlgebra K n, ∃ m : ℕ, ∃ b : Fin m → EnvelopingAlgebra K n,
      ∃ c : Fin m → SmoothFunctions K n,
        ∀ g, envelopingConjugation K n g a = ∑ i, ((c i).val g) • b i := by
  intro a
  change HasFiniteSmoothCoefficients K n a
  refine Quotient.inductionOn a ?_
  intro t
  let q := UniversalEnvelopingAlgebra.mkAlgHom ℂ (ComplexLieAlgebra K n)
  change HasFiniteSmoothCoefficients K n (q t)
  induction t using TensorAlgebra.induction with
  | algebraMap z =>
    simpa only [AlgHom.commutes] using coefficients_scalar K n z
  | ι X =>
    exact coefficients_complex_generator K n X
  | mul a b ha hb =>
    rw [map_mul]
    exact coefficients_mul K n _ _ ha hb
  | add a b ha hb =>
    rw [map_add]
    exact coefficients_add K n _ _ ha hb

end Langlands.Global.ArchimedeanGL
