import Langlands.HarmonicAnalysis.RowFourier
import Langlands.HarmonicAnalysis.RowSchwartzAction
import Langlands.Representation.RankinSelberg.Measures

/-! Concrete rectangular coordinates, right action, and raw Fourier integrals. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Langlands.HarmonicAnalysis

universe uK

section Coordinates

variable {K : Type uK} {n : ℕ}

/-- The first `n` columns of an actual `n × (n+1)` matrix. -/
def rectangularFirstColumns (m : Matrix (Fin n) (Fin (n + 1)) K) :
    Matrix (Fin n) (Fin n) K := fun i j => m i j.castSucc

/-- The last column of an actual `n × (n+1)` matrix. -/
def rectangularLastColumn (m : Matrix (Fin n) (Fin (n + 1)) K) : Fin n → K :=
  fun i => m i (Fin.last n)

/-- The actual matrix `[x,y]`, with square first block `x` and last column `y`. -/
def rectangularJoin (x : Matrix (Fin n) (Fin n) K) (y : Fin n → K) :
    Matrix (Fin n) (Fin (n + 1)) K :=
  fun i j => Fin.lastCases (y i) (fun k => x i k) j

@[simp] theorem rectangularJoin_castSucc (x : Matrix (Fin n) (Fin n) K)
    (y : Fin n → K) (i j : Fin n) : rectangularJoin x y i j.castSucc = x i j := by
  simp [rectangularJoin]

@[simp] theorem rectangularJoin_last (x : Matrix (Fin n) (Fin n) K)
    (y : Fin n → K) (i : Fin n) : rectangularJoin x y i (Fin.last n) = y i := by
  simp [rectangularJoin]

@[simp] theorem rectangularFirstColumns_join (x : Matrix (Fin n) (Fin n) K)
    (y : Fin n → K) : rectangularFirstColumns (rectangularJoin x y) = x := by
  ext i j
  simp [rectangularFirstColumns]

@[simp] theorem rectangularLastColumn_join (x : Matrix (Fin n) (Fin n) K)
    (y : Fin n → K) : rectangularLastColumn (rectangularJoin x y) = y := by
  ext i
  simp [rectangularLastColumn]

@[simp] theorem rectangularJoin_split (m : Matrix (Fin n) (Fin (n + 1)) K) :
    rectangularJoin (rectangularFirstColumns m) (rectangularLastColumn m) = m := by
  ext i j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp [rectangularLastColumn]
  · simp [rectangularFirstColumns]

variable [TopologicalSpace K]

theorem continuous_rectangularFirstColumns :
    Continuous (rectangularFirstColumns (K := K) (n := n)) := by
  exact continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply j.castSucc).comp (continuous_apply i)

theorem continuous_rectangularLastColumn :
    Continuous (rectangularLastColumn (K := K) (n := n)) := by
  exact continuous_pi fun i => (continuous_apply (Fin.last n)).comp (continuous_apply i)

theorem continuous_rectangularJoin : Continuous (fun p :
    Matrix (Fin n) (Fin n) K × (Fin n → K) => rectangularJoin p.1 p.2) := by
  apply continuous_matrix
  intro i j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp only [rectangularJoin_last]
    exact (continuous_apply i).comp continuous_snd
  · simp only [rectangularJoin_castSucc]
    exact continuous_fst.matrix_elem i k

/-- Splitting off the last column is a homeomorphism on the actual matrix space. -/
def rectangularSplit : Matrix (Fin n) (Fin (n + 1)) K ≃ₜ
    Matrix (Fin n) (Fin n) K × (Fin n → K) where
  toFun m := (rectangularFirstColumns m, rectangularLastColumn m)
  invFun p := rectangularJoin p.1 p.2
  left_inv := rectangularJoin_split
  right_inv p := by simp
  continuous_toFun := continuous_rectangularFirstColumns.prodMk continuous_rectangularLastColumn
  continuous_invFun := continuous_rectangularJoin

@[simp] theorem rectangularSplit_apply (m : Matrix (Fin n) (Fin (n + 1)) K) :
    rectangularSplit m = (rectangularFirstColumns m, rectangularLastColumn m) := rfl

@[simp] theorem rectangularSplit_symm_apply (x : Matrix (Fin n) (Fin n) K)
    (y : Fin n → K) : rectangularSplit.symm (x,y) = rectangularJoin x y := rfl

/-- A fixed-first-block slice has compact support: its support lies in the
compact last-column projection of the original support. -/
theorem rectangularSlice_hasCompactSupport [T2Space K]
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K))
    (x : Matrix (Fin n) (Fin n) K) :
    HasCompactSupport (fun u => Φ (rectangularJoin x u)) := by
  have hc : IsCompact (rectangularLastColumn '' tsupport
      (Φ : Matrix (Fin n) (Fin (n + 1)) K → ℂ)) :=
    Φ.hasCompactSupport.image continuous_rectangularLastColumn
  apply HasCompactSupport.intro hc
  intro u hu
  by_contra hn
  apply hu
  exact ⟨rectangularJoin x u, subset_tsupport _ hn, rectangularLastColumn_join x u⟩

/-- The actual Schwartz function on a fixed last-column slice. -/
def rectangularSlice [T2Space K]
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K))
    (x : Matrix (Fin n) (Fin n) K) : SchwartzBruhat (Fin n → K) :=
  ⟨fun u => Φ (rectangularJoin x u),
    Φ.locallyConstant.comp_continuous
      (continuous_rectangularJoin.comp (continuous_const.prodMk continuous_id)),
    rectangularSlice_hasCompactSupport Φ x⟩

@[simp] theorem rectangularSlice_apply [T2Space K]
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K))
    (x : Matrix (Fin n) (Fin n) K) (u : Fin n → K) :
    rectangularSlice Φ x u = Φ (rectangularJoin x u) := rfl

end Coordinates

section RightAction

variable {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  {r s : ℕ}

/-- Right multiplication by an actual invertible matrix, in any rectangular rank. -/
def rectangularHomeomorph (g : Langlands.GeneralLinear s K) :
    Matrix (Fin r) (Fin s) K ≃ₜ Matrix (Fin r) (Fin s) K where
  toFun m := m * g.val
  invFun m := m * (g⁻¹).val
  left_inv m := by
    dsimp only
    rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  right_inv m := by
    dsimp only
    rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
  continuous_toFun := continuous_id.matrix_mul continuous_const
  continuous_invFun := continuous_id.matrix_mul continuous_const

@[simp] theorem rectangularHomeomorph_apply (g : Langlands.GeneralLinear s K)
    (m : Matrix (Fin r) (Fin s) K) : rectangularHomeomorph g m = m * g.val := rfl

/-- Right translation with the JPSS convention `(R_g Φ)(m) = Φ(mg)`. -/
def rectangularTranslate (g : Langlands.GeneralLinear s K) :
    SchwartzBruhat (Matrix (Fin r) (Fin s) K) ≃ₗ[ℂ]
      SchwartzBruhat (Matrix (Fin r) (Fin s) K) :=
  Hecke.TestFunction.pullback (rectangularHomeomorph g)

@[simp] theorem rectangularTranslate_apply (g : Langlands.GeneralLinear s K)
    (Φ : SchwartzBruhat (Matrix (Fin r) (Fin s) K)) (m : Matrix (Fin r) (Fin s) K) :
    rectangularTranslate g Φ m = Φ (m * g.val) := rfl

@[simp] theorem rectangularTranslate_one
    (Φ : SchwartzBruhat (Matrix (Fin r) (Fin s) K)) : rectangularTranslate 1 Φ = Φ := by
  ext m
  simp

theorem rectangularTranslate_mul (g h : Langlands.GeneralLinear s K)
    (Φ : SchwartzBruhat (Matrix (Fin r) (Fin s) K)) :
    rectangularTranslate (g * h) Φ = rectangularTranslate g (rectangularTranslate h Φ) := by
  ext m
  simp only [rectangularTranslate_apply, Units.val_mul, Matrix.mul_assoc]

/-- The representation on actual rectangular Schwartz functions, including `n × (n+1)`. -/
def rectangularSchwartzRepresentation : Representation ℂ (Langlands.GeneralLinear s K)
    (SchwartzBruhat (Matrix (Fin r) (Fin s) K)) where
  toFun g := (rectangularTranslate g).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro Φ
    exact rectangularTranslate_one Φ
  map_mul' g h := by
    apply LinearMap.ext
    intro Φ
    exact rectangularTranslate_mul g h Φ

@[simp] theorem rectangularSchwartzRepresentation_apply (g : Langlands.GeneralLinear s K)
    (Φ : SchwartzBruhat (Matrix (Fin r) (Fin s) K)) :
    rectangularSchwartzRepresentation g Φ = rectangularTranslate g Φ := rfl

end RightAction

section FullFourier

variable {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] {r s : ℕ}

/-- The entry pairing, without a sign or conjugation, in arbitrary rectangular rank. -/
def rectangularPairing (a b : Matrix (Fin r) (Fin s) K) : K := ∑ i, ∑ j, a i j * b i j

omit [MeasurableSpace K] in
theorem continuous_rectangularPairing_left (b : Matrix (Fin r) (Fin s) K) :
    Continuous (fun a => rectangularPairing a b) := by
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (continuous_id.matrix_elem i j).mul continuous_const

/-- The raw full plus-sign Fourier integral, with the supplied product Haar measure. -/
def rectangularFourierIntegral (ψ : UnitaryAdditiveCharacter K) (μ : AdditiveHaarMeasure K)
    (f : Matrix (Fin r) (Fin s) K → ℂ) (b : Matrix (Fin r) (Fin s) K) : ℂ :=
  ∫ a, f a * ψ.complex (rectangularPairing a b) ∂RankinSelberg.rectangularMeasure μ r s

variable [BorelSpace (Matrix (Fin r) (Fin s) K)]

theorem rectangularFourierIntegrand_integrable (ψ : UnitaryAdditiveCharacter K)
    (μ : AdditiveHaarMeasure K) [SigmaFinite μ.measure]
    (Φ : SchwartzBruhat (Matrix (Fin r) (Fin s) K)) (b : Matrix (Fin r) (Fin s) K) :
    Integrable (fun a => Φ a * ψ.complex (rectangularPairing a b))
      (RankinSelberg.rectangularMeasure μ r s) := by
  have : IsFiniteMeasureOnCompacts (RankinSelberg.rectangularMeasure μ r s) :=
    inferInstanceAs (IsFiniteMeasureOnCompacts
      (Measure.pi (fun _ : Fin r => Measure.pi (fun _ : Fin s => μ.measure))))
  exact (Φ.continuous.mul (ψ.continuous_complex.comp
    (continuous_rectangularPairing_left b))).integrable_of_hasCompactSupport
      Φ.hasCompactSupport.mul_right

/-- Complex-linear raw full Fourier transform into all functions. -/
def rectangularFourierTransform (ψ : UnitaryAdditiveCharacter K)
    (μ : AdditiveHaarMeasure K) [SigmaFinite μ.measure] :
    SchwartzBruhat (Matrix (Fin r) (Fin s) K) →ₗ[ℂ]
      (Matrix (Fin r) (Fin s) K → ℂ) where
  toFun Φ := rectangularFourierIntegral ψ μ Φ
  map_add' Φ Ψ := by
    ext b
    change (∫ a, (Φ a + Ψ a) * ψ.complex (rectangularPairing a b)
        ∂RankinSelberg.rectangularMeasure μ r s) = _
    simp_rw [add_mul]
    exact integral_add (rectangularFourierIntegrand_integrable ψ μ Φ b)
      (rectangularFourierIntegrand_integrable ψ μ Ψ b)
  map_smul' c Φ := by
    ext b
    change (∫ a, (c * Φ a) * ψ.complex (rectangularPairing a b)
        ∂RankinSelberg.rectangularMeasure μ r s) =
      c * ∫ a, Φ a * ψ.complex (rectangularPairing a b)
        ∂RankinSelberg.rectangularMeasure μ r s
    simp_rw [mul_assoc]
    exact integral_const_mul c _

@[simp] theorem rectangularFourierTransform_apply (ψ : UnitaryAdditiveCharacter K)
    (μ : AdditiveHaarMeasure K) [SigmaFinite μ.measure]
    (Φ : SchwartzBruhat (Matrix (Fin r) (Fin s) K)) (b : Matrix (Fin r) (Fin s) K) :
    rectangularFourierTransform ψ μ Φ b = rectangularFourierIntegral ψ μ Φ b := rfl

end FullFourier

section PartialFourier

variable {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] {n : ℕ}

/-- Raw partial Fourier integral in the last column, using the inverse character. -/
def partialFourierIntegral (ψ : UnitaryAdditiveCharacter K) (μ : AdditiveHaarMeasure K)
    (f : Matrix (Fin n) (Fin (n + 1)) K → ℂ) (m : Matrix (Fin n) (Fin (n + 1)) K) : ℂ :=
  ∫ u, f (rectangularJoin (rectangularFirstColumns m) u) *
    ψ.complex (-rowPairing (rectangularLastColumn m) u) ∂rowMeasure μ n

/-- Opposite-sign raw partial integral, reserved for the later inversion theorem. -/
def partialFourierPlusIntegral (ψ : UnitaryAdditiveCharacter K) (μ : AdditiveHaarMeasure K)
    (f : Matrix (Fin n) (Fin (n + 1)) K → ℂ) (m : Matrix (Fin n) (Fin (n + 1)) K) : ℂ :=
  ∫ u, f (rectangularJoin (rectangularFirstColumns m) u) *
    ψ.complex (rowPairing (rectangularLastColumn m) u) ∂rowMeasure μ n

omit [IsTopologicalRing K] in
@[simp] theorem partialFourierIntegral_join (ψ : UnitaryAdditiveCharacter K)
    (μ : AdditiveHaarMeasure K) (f : Matrix (Fin n) (Fin (n + 1)) K → ℂ)
    (x : Matrix (Fin n) (Fin n) K) (y : Fin n → K) :
    partialFourierIntegral ψ μ f (rectangularJoin x y) =
      ∫ u, f (rectangularJoin x u) * ψ.complex (-(∑ i, y i * u i)) ∂rowMeasure μ n := by
  simp [partialFourierIntegral, rowPairing]

omit [IsTopologicalRing K] in
@[simp] theorem partialFourierPlusIntegral_join (ψ : UnitaryAdditiveCharacter K)
    (μ : AdditiveHaarMeasure K) (f : Matrix (Fin n) (Fin (n + 1)) K → ℂ)
    (x : Matrix (Fin n) (Fin n) K) (y : Fin n → K) :
    partialFourierPlusIntegral ψ μ f (rectangularJoin x y) =
      ∫ u, f (rectangularJoin x u) * ψ.complex (∑ i, y i * u i) ∂rowMeasure μ n := by
  simp [partialFourierPlusIntegral, rowPairing]

variable [T2Space K] [BorelSpace (Fin n → K)]

theorem partialFourierIntegrand_integrable (ψ : UnitaryAdditiveCharacter K)
    (μ : AdditiveHaarMeasure K) [SigmaFinite μ.measure]
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K))
    (m : Matrix (Fin n) (Fin (n + 1)) K) :
    Integrable (fun u => Φ (rectangularJoin (rectangularFirstColumns m) u) *
      ψ.complex (-rowPairing (rectangularLastColumn m) u)) (rowMeasure μ n) := by
  have hc : Continuous (fun u => rowPairing (rectangularLastColumn m) u) :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)
  exact ((rectangularSlice Φ (rectangularFirstColumns m)).continuous.mul
    (ψ.continuous_complex.comp hc.neg)).integrable_of_hasCompactSupport
      (rectangularSlice_hasCompactSupport Φ (rectangularFirstColumns m)).mul_right

theorem partialFourierPlusIntegrand_integrable (ψ : UnitaryAdditiveCharacter K)
    (μ : AdditiveHaarMeasure K) [SigmaFinite μ.measure]
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K))
    (m : Matrix (Fin n) (Fin (n + 1)) K) :
    Integrable (fun u => Φ (rectangularJoin (rectangularFirstColumns m) u) *
      ψ.complex (rowPairing (rectangularLastColumn m) u)) (rowMeasure μ n) := by
  have hc : Continuous (fun u => rowPairing (rectangularLastColumn m) u) :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)
  exact ((rectangularSlice Φ (rectangularFirstColumns m)).continuous.mul
    (ψ.continuous_complex.comp hc)).integrable_of_hasCompactSupport
      (rectangularSlice_hasCompactSupport Φ (rectangularFirstColumns m)).mul_right

/-- The inverse-character raw partial Fourier transform, into all functions. -/
def partialFourierTransform (ψ : UnitaryAdditiveCharacter K) (μ : AdditiveHaarMeasure K)
    [SigmaFinite μ.measure] : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K) →ₗ[ℂ]
      (Matrix (Fin n) (Fin (n + 1)) K → ℂ) where
  toFun Φ := partialFourierIntegral ψ μ Φ
  map_add' Φ Ψ := by
    ext m
    change (∫ u, (Φ (rectangularJoin (rectangularFirstColumns m) u) +
        Ψ (rectangularJoin (rectangularFirstColumns m) u)) *
        ψ.complex (-rowPairing (rectangularLastColumn m) u) ∂rowMeasure μ n) = _
    simp_rw [add_mul]
    exact integral_add (partialFourierIntegrand_integrable ψ μ Φ m)
      (partialFourierIntegrand_integrable ψ μ Ψ m)
  map_smul' c Φ := by
    ext m
    change (∫ u, (c * Φ (rectangularJoin (rectangularFirstColumns m) u)) *
        ψ.complex (-rowPairing (rectangularLastColumn m) u) ∂rowMeasure μ n) =
      c * ∫ u, Φ (rectangularJoin (rectangularFirstColumns m) u) *
        ψ.complex (-rowPairing (rectangularLastColumn m) u) ∂rowMeasure μ n
    simp_rw [mul_assoc]
    exact integral_const_mul c _

/-- The plus-character companion, into all functions. -/
def partialFourierPlusTransform (ψ : UnitaryAdditiveCharacter K) (μ : AdditiveHaarMeasure K)
    [SigmaFinite μ.measure] : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K) →ₗ[ℂ]
      (Matrix (Fin n) (Fin (n + 1)) K → ℂ) where
  toFun Φ := partialFourierPlusIntegral ψ μ Φ
  map_add' Φ Ψ := by
    ext m
    change (∫ u, (Φ (rectangularJoin (rectangularFirstColumns m) u) +
        Ψ (rectangularJoin (rectangularFirstColumns m) u)) *
        ψ.complex (rowPairing (rectangularLastColumn m) u) ∂rowMeasure μ n) = _
    simp_rw [add_mul]
    exact integral_add (partialFourierPlusIntegrand_integrable ψ μ Φ m)
      (partialFourierPlusIntegrand_integrable ψ μ Ψ m)
  map_smul' c Φ := by
    ext m
    change (∫ u, (c * Φ (rectangularJoin (rectangularFirstColumns m) u)) *
        ψ.complex (rowPairing (rectangularLastColumn m) u) ∂rowMeasure μ n) =
      c * ∫ u, Φ (rectangularJoin (rectangularFirstColumns m) u) *
        ψ.complex (rowPairing (rectangularLastColumn m) u) ∂rowMeasure μ n
    simp_rw [mul_assoc]
    exact integral_const_mul c _

@[simp] theorem partialFourierTransform_apply (ψ : UnitaryAdditiveCharacter K)
    (μ : AdditiveHaarMeasure K) [SigmaFinite μ.measure]
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K))
    (m : Matrix (Fin n) (Fin (n + 1)) K) :
    partialFourierTransform ψ μ Φ m = partialFourierIntegral ψ μ Φ m := rfl

@[simp] theorem partialFourierPlusTransform_apply (ψ : UnitaryAdditiveCharacter K)
    (μ : AdditiveHaarMeasure K) [SigmaFinite μ.measure]
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K))
    (m : Matrix (Fin n) (Fin (n + 1)) K) :
    partialFourierPlusTransform ψ μ Φ m = partialFourierPlusIntegral ψ μ Φ m := rfl

end PartialFourier

end Langlands.HarmonicAnalysis
