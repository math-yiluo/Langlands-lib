import Langlands.BaseChange.SigmaLiftCharacterIdentity.Localization
import Langlands.LocalField.SmoothCharacterNormProof
import Langlands.Representation.Hecke.MassIndicatorProducts
import Langlands.Representation.RankinSelberg.DeterminantSlices
import Langlands.Representation.Unramified.StandardMonomialSupport

/-! # Determinant-order slices of spherical Hecke functions -/

noncomputable section

namespace Langlands.BaseChange

open HarmonicAnalysis MeasureTheory Unramified

universe u

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (r : ℕ)

/-- The normalized integer order of the actual determinant. -/
def matrixDeterminantOrder (g : GeneralLinear (r + 1) F.Carrier) : ℤ :=
  F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier)

theorem continuous_matrixDeterminantOrder : Continuous (matrixDeterminantOrder F r) :=
  (RankinSelberg.continuous_ord_units F.canonicalTopologicalData).comp
    (F.canonicalTopologicalData.generalLinearDeterminant (r + 1)).continuous

theorem matrixDeterminantOrder_mul (x y : GeneralLinear (r + 1) F.Carrier) :
    matrixDeterminantOrder F r (x * y) = matrixDeterminantOrder F r x + matrixDeterminantOrder F r y := by
  unfold matrixDeterminantOrder
  rw [map_mul, Units.val_mul, F.canonicalTopologicalData.ord_mul (Units.ne_zero _) (Units.ne_zero _)]

theorem matrixDeterminantOrder_eq_zero_of_mem_spherical
    (k : sphericalOpenSubgroup F r) : matrixDeterminantOrder F r k.val = 0 := by
  exact (F.canonicalTopologicalData.ord_eq_zero_iff_normalizedAbs _).2
    ((F.canonicalTopologicalData.normalizedAbs_eq_one_iff_valuation_eq_one _).2
      (valuation_det_of_mem_spherical k.property))

private theorem isClopen_detOrder (m : ℤ) :
    IsClopen (matrixDeterminantOrder F r ⁻¹' ({m} : Set ℤ)) :=
  (isClopen_discrete _).preimage (continuous_matrixDeterminantOrder F r)

private theorem cutoff_detOrder_apply (f : SchwartzBruhat (GeneralLinear (r + 1) F.Carrier))
    (m : ℤ) (g : GeneralLinear (r + 1) F.Carrier) :
    ConcordanceLocalization.cutoff (isClopen_detOrder F r m) f g =
      if matrixDeterminantOrder F r g = m then f g else 0 := by
  rw [ConcordanceLocalization.cutoff_apply]
  simp only [Set.mem_preimage, Set.mem_singleton_iff]

/-- Restrict a spherical Hecke function to a single determinant order. -/
def sphericalDeterminantSlice (φ : SphericalHeckeAlgebra F r) (m : ℤ) :
    SphericalHeckeAlgebra F r := by
  let f : SchwartzBruhat (GeneralLinear (r + 1) F.Carrier) :=
    ConcordanceLocalization.cutoff (isClopen_detOrder F r m) φ.val
  have hf (x : GeneralLinear (r + 1) F.Carrier) :
      f x = if matrixDeterminantOrder F r x = m then φ x else 0 :=
    cutoff_detOrder_apply F r φ.val m x
  refine ⟨f, ?_, ?_⟩
  · intro k x
    change f (k.val * x) = f x
    rw [hf, hf, matrixDeterminantOrder_mul, matrixDeterminantOrder_eq_zero_of_mem_spherical F r k,
      zero_add]
    have hk : φ (k.val * x) = φ x := φ.property.1 k x
    rw [hk]
  · intro k x
    change f (x * k.val) = f x
    rw [hf, hf, matrixDeterminantOrder_mul, matrixDeterminantOrder_eq_zero_of_mem_spherical F r k,
      add_zero]
    have hk : φ (x * k.val) = φ x := φ.property.2 k x
    rw [hk]

@[simp] theorem sphericalDeterminantSlice_apply (φ : SphericalHeckeAlgebra F r) (m : ℤ)
    (g : GeneralLinear (r + 1) F.Carrier) :
    sphericalDeterminantSlice F r φ m g = if matrixDeterminantOrder F r g = m then φ g else 0 := by
  exact cutoff_detOrder_apply F r φ.val m g

/-- Every spherical Hecke function is a finite sum of its determinant-order slices. -/
def SphericalDeterminantSlicesStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (r : ℕ) (φ : SphericalHeckeAlgebra F r),
    ∃ orders : Finset ℤ, φ = ∑ m ∈ orders, sphericalDeterminantSlice F r φ m

theorem sphericalDeterminantSlices : SphericalDeterminantSlicesStatement.{u} := by
  intro p hp F r φ
  classical
  have hcompact : HasCompactSupport ⇑φ := φ.val.hasCompactSupport
  have hfinite : (matrixDeterminantOrder F r '' tsupport ⇑φ).Finite :=
    (hcompact.image (continuous_matrixDeterminantOrder F r)).finite_of_discrete
  refine ⟨hfinite.toFinset, ?_⟩
  apply Hecke.HeckeAlgebra.Corner.ext'
  intro g
  let eval := Hecke.HeckeAlgebra.Corner.evalLinear (sphericalOpenSubgroup F r)
    (sphericalOpenSubgroup_isCompact F r) (sphericalHaar F r) g
  change φ g = eval (∑ m ∈ hfinite.toFinset, sphericalDeterminantSlice F r φ m)
  rw [map_sum]
  change φ g = ∑ m ∈ hfinite.toFinset, sphericalDeterminantSlice F r φ m g
  simp only [sphericalDeterminantSlice_apply]
  by_cases hg : φ g = 0
  · simp [hg]
  have hm : matrixDeterminantOrder F r g ∈ hfinite.toFinset :=
    hfinite.mem_toFinset.mpr ⟨g, subset_tsupport φ hg, rfl⟩
  rw [Finset.sum_eq_single_of_mem _ hm]
  · simp
  · intro m _ hne
    simp [Ne.symm hne]

end Langlands.BaseChange
