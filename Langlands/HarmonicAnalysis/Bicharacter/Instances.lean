import Langlands.HarmonicAnalysis.Bicharacter.Fourier
import Langlands.HarmonicAnalysis.RectangularFourier
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

/-!
# The Library's Fourier transforms as transforms of self-dual bicharacters

The Library's scalar, row and rectangular Fourier integrals (`fourierIntegral`,
`rowFourierIntegral`, `rectangularFourierIntegral`) are the transforms `bicharacterFourier` of the
bicharacters `(a, b) ↦ ψ(a b)`, `ψ(∑ aᵢ bᵢ)`, `ψ(∑ aᵢⱼ bᵢⱼ)` for the Library's measures
(`fourierIntegral_eq_bicharacterFourier`, `rowFourierIntegral_eq_bicharacterFourier`,
`rectangularFourierIntegral_eq_bicharacterFourier`). Over a nonarchimedean local field these
bicharacters are self-dual (`isSelfDualBicharacter_mul`, `isSelfDualBicharacter_rowPairing`,
`isSelfDualBicharacter_rectangularPairing`), so the general theory applies to them: for instance
the row transform preserves Schwartz–Bruhat functions for every Haar measure (`rowFourierClosed`),
and the Library's scalar self-duality `IsSelfDual ψ μ` says that the constant of
`exists_pos_bicharacterFourier_bicharacterFourier` is `1` (`isSelfDual_iff`).
-/

noncomputable section

open MeasureTheory

namespace Langlands.HarmonicAnalysis

section Field

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [MeasurableSpace K]

omit [IsTopologicalRing K] in
/-- The scalar Fourier integral is the transform of the bicharacter `(a, b) ↦ ψ(a b)`. -/
theorem fourierIntegral_eq_bicharacterFourier (ψ : UnitaryAdditiveCharacter K)
    (μ : AdditiveHaarMeasure K) (f : K → ℂ) (y : K) :
    fourierIntegral ψ μ f y = bicharacterFourier μ.measure (fun a b => ψ.complex (a * b)) f y := by
  simp only [fourierIntegral, bicharacterFourier, mul_comm y]

omit [IsTopologicalRing K] in
theorem rowPairing_comm [BorelSpace K] {d : ℕ} (x y : Fin d → K) :
    rowPairing x y = rowPairing y x := by
  simp only [rowPairing, mul_comm]

omit [IsTopologicalRing K] in
/-- The row Fourier integral is the transform of the bicharacter `(a, b) ↦ ψ(∑ aᵢ bᵢ)`. -/
theorem rowFourierIntegral_eq_bicharacterFourier [BorelSpace K] (ψ : UnitaryAdditiveCharacter K)
    (μ : AdditiveHaarMeasure K) (d : ℕ) (f : (Fin d → K) → ℂ) (y : Fin d → K) :
    rowFourierIntegral ψ μ d f y =
      bicharacterFourier (rowMeasure μ d) (fun a b => ψ.complex (rowPairing a b)) f y := by
  simp only [rowFourierIntegral, bicharacterFourier, rowPairing_comm y]

omit [IsTopologicalRing K] in
/-- The rectangular Fourier integral is the transform of the bicharacter
`(a, b) ↦ ψ(∑ aᵢⱼ bᵢⱼ)` for the Library's product measure. -/
theorem rectangularFourierIntegral_eq_bicharacterFourier (ψ : UnitaryAdditiveCharacter K)
    (μ : AdditiveHaarMeasure K) {r s : ℕ} (f : Matrix (Fin r) (Fin s) K → ℂ)
    (b : Matrix (Fin r) (Fin s) K) :
    rectangularFourierIntegral ψ μ f b =
      bicharacterFourier (RankinSelberg.rectangularMeasure μ r s)
        (fun a b => ψ.complex (rectangularPairing a b)) f b := by
  simp only [rectangularFourierIntegral, bicharacterFourier, rectangularPairing, mul_comm]

end Field

section LocalField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]

omit [MeasurableSpace K] [BorelSpace K] in
/-- `(a, b) ↦ ψ(a b)` is a self-dual bicharacter of a nonarchimedean local field. -/
theorem isSelfDualBicharacter_mul (ψ : UnitaryAdditiveCharacter K) :
    IsSelfDualBicharacter fun a b : K => ψ.complex (a * b) :=
  isSelfDualBicharacter_of_symm ψ.continuous_complex ψ.norm_complex ψ.complex_ne_one
    (LinearMap.mul K K) (fun x y => mul_comm x y) fun y hy => by simpa using hy 1

omit [MeasurableSpace K] [BorelSpace K] in
/-- `(a, b) ↦ ψ(∑ aᵢ bᵢ)` is a self-dual bicharacter of `Kᵈ`. -/
theorem isSelfDualBicharacter_rowPairing (ψ : UnitaryAdditiveCharacter K) (d : ℕ) :
    IsSelfDualBicharacter fun a b : Fin d → K => ψ.complex (rowPairing a b) := by
  have h := isSelfDualBicharacter_of_symm (V := Fin d → K) ψ.continuous_complex ψ.norm_complex
    ψ.complex_ne_one (dotProductBilin K K) (fun x y => dotProduct_comm x y)
    fun y hy => funext fun i => by simpa using hy (Pi.single i 1)
  simpa [rowPairing, dotProduct] using h

omit [MeasurableSpace K] [BorelSpace K] in
/-- `(a, b) ↦ ψ(∑ aᵢⱼ bᵢⱼ)` is a self-dual bicharacter of `M_{r×s}(K)`. -/
theorem isSelfDualBicharacter_rectangularPairing (ψ : UnitaryAdditiveCharacter K) (r s : ℕ) :
    IsSelfDualBicharacter fun a b : Matrix (Fin r) (Fin s) K =>
      ψ.complex (rectangularPairing a b) := by
  have : IsModuleTopology K (Matrix (Fin r) (Fin s) K) :=
    inferInstanceAs (IsModuleTopology K (Fin r → Fin s → K))
  let β : Matrix (Fin r) (Fin s) K →ₗ[K] Matrix (Fin r) (Fin s) K →ₗ[K] K :=
    LinearMap.mk₂ K rectangularPairing
      (fun a a' b => by simp [rectangularPairing, add_mul, Finset.sum_add_distrib])
      (fun c a b => by simp [rectangularPairing, Finset.mul_sum, mul_assoc])
      (fun a b b' => by simp [rectangularPairing, mul_add, Finset.sum_add_distrib])
      (fun c a b => by simp [rectangularPairing, Finset.mul_sum, mul_left_comm])
  have h := isSelfDualBicharacter_of_symm (V := Matrix (Fin r) (Fin s) K) ψ.continuous_complex
    ψ.norm_complex ψ.complex_ne_one β
    (fun x y => show rectangularPairing x y = rectangularPairing y x by
      simp only [rectangularPairing, mul_comm])
    fun y hy => by
      ext i j
      have := hy (Matrix.single i j 1)
      change rectangularPairing (Matrix.single i j 1) y = 0 at this
      simpa [rectangularPairing, Matrix.single_apply, ite_and, Finset.sum_ite_eq,
        Finset.sum_ite_eq'] using this
  exact h

/-- The row transform preserves Schwartz–Bruhat functions, for every Haar measure. -/
theorem rowFourierClosed (ψ : UnitaryAdditiveCharacter K) (μ : AdditiveHaarMeasure K) (d : ℕ) :
    RowFourierClosed ψ μ d := by
  have := GeneralLocalField.secondCountableTopology K
  have : SigmaFinite μ.measure := sigmaFinite_of_locallyFinite
  intro f
  refine ⟨⟨_, bicharacterFourier_mem (rowMeasure μ d) (isSelfDualBicharacter_rowPairing ψ d)
    f.2⟩, fun y => ?_⟩
  rw [rowFourierIntegral_eq_bicharacterFourier]

/-- The Library's scalar self-duality says that the Fourier transform of `(a, b) ↦ ψ(a b)` squares
to the reflection, that is, the constant of `exists_pos_bicharacterFourier_bicharacterFourier`
is `1`. -/
theorem isSelfDual_iff (ψ : UnitaryAdditiveCharacter K) (μ : AdditiveHaarMeasure K) :
    IsSelfDual ψ μ ↔ ∀ φ ∈ schwartzBruhatSubmodule K, ∀ x,
      bicharacterFourier μ.measure (fun a b => ψ.complex (a * b))
        (bicharacterFourier μ.measure (fun a b => ψ.complex (a * b)) φ) x = φ (-x) := by
  have := GeneralLocalField.secondCountableTopology K
  have he := isSelfDualBicharacter_mul ψ
  constructor
  · intro h φ hφ x
    have := (h ⟨φ, hφ⟩).2 x
    simp only [fourierTransform, LinearMap.coe_mk, AddHom.coe_mk] at this
    rw [← this, fourierIntegral_eq_bicharacterFourier]
    congr 1
    funext y
    exact (fourierIntegral_eq_bicharacterFourier ψ μ φ y).symm
  · intro h f
    have hmem := bicharacterFourier_mem μ.measure he f.2
    have hF : (fourierTransform ψ μ f : K → ℂ) =
        bicharacterFourier μ.measure (fun a b => ψ.complex (a * b)) f := by
      funext y
      exact fourierIntegral_eq_bicharacterFourier ψ μ f y
    refine ⟨fun y => ?_, fun x => ?_⟩
    · rw [hF]
      exact ((ψ.continuous_complex.comp (continuous_id.mul continuous_const)).mul
        hmem.1.continuous).integrable_of_hasCompactSupport hmem.2.mul_left
    · rw [fourierIntegral_eq_bicharacterFourier, hF]
      exact h f f.2 x

end LocalField

end Langlands.HarmonicAnalysis
