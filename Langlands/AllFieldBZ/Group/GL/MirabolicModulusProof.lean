import Langlands.AllFieldBZ.Group.GL.MirabolicRadical
import Langlands.AllFieldBZ.HarmonicAnalysis.PadicRectangularHaarScalingProof
import Langlands.Group.GL.MirabolicModulusProof

/-!
# All-field port of `Langlands.Group.GL.MirabolicModulusProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Group.GL.MirabolicModulusProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open MeasureTheory
open MeasureTheory.Measure
open scoped NNReal
open scoped ENNReal
namespace Langlands.AllFieldBZ
universe uF

/-- The multiplicative type synonym carries the measurable structure of the
underlying type. -/
local instance multiplicativeMeasurableSpace {A : Type*} [MeasurableSpace A] :
    MeasurableSpace (Multiplicative A) := ‹MeasurableSpace A›

local instance multiplicativeBorelSpace {A : Type*} [TopologicalSpace A]
    [MeasurableSpace A] [BorelSpace A] : BorelSpace (Multiplicative A) :=
  ‹BorelSpace A›

/-- A Haar measure on `Multiplicative A` is an additive Haar measure on `A`. -/
private theorem _root_.Langlands.multiplicativeHaar_isAddHaar
    {A : Type*} [AddGroup A] [TopologicalSpace A] [MeasurableSpace A]
    (μ : Measure (Multiplicative A)) [IsHaarMeasure μ] :
    IsAddHaarMeasure (show Measure A from μ) where
  toIsFiniteMeasureOnCompacts := (inferInstance : IsFiniteMeasureOnCompacts μ)
  toIsOpenPosMeasure := (inferInstance : IsOpenPosMeasure μ)
  map_add_left_eq_self g := map_mul_left_eq_self μ (Multiplicative.ofAdd g)

namespace GeneralLinear.Mirabolic
open Langlands.GeneralLinear.Mirabolic hiding leviRadical_haarCharacter radicalCoordinates_isAddHaar radicalHaar_map_leviConj
section Coordinates
variable {K : Type*} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    {n : ℕ}

end Coordinates
variable (F : LocalFieldPackage.{uF}) (T : F.TopologicalData)

/-- Actual radical Haar measure becomes additive Haar measure in last-column
coordinates, for every Borel measurable structure on the coordinate space. The
supplied field topology is retained. -/
theorem radicalCoordinates_isAddHaar (n : ℕ) :
    letI := T.topology
    letI : MeasurableSpace (radical n F.Carrier) := borel _
    ∀ [MeasurableSpace (Fin n → F.Carrier)] [BorelSpace (Fin n → F.Carrier)]
      (μ : Measure (radical n F.Carrier)) [IsHaarMeasure μ],
      IsAddHaarMeasure (μ.map radicalCoordinates) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let : MeasurableSpace (radical n F.Carrier) := borel _
  let : BorelSpace (radical n F.Carrier) := ⟨rfl⟩
  intro _ _ μ hμ
  have h := (radicalContinuousEquiv (n := n) (F := F.Carrier)).isHaarMeasure_map μ
  exact @multiplicativeHaar_isAddHaar (Fin n → F.Carrier) _ _ _
    (μ.map (radicalContinuousEquiv (n := n) (F := F.Carrier))) h

/-- Pushforward by actual Levi conjugation scales every Borel radical Haar
measure by the inverse determinant norm. -/
theorem radicalHaar_map_leviConj (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI : MeasurableSpace (radical n F.Carrier) := borel _
    ∀ (μ : Measure (radical n F.Carrier)) [IsHaarMeasure μ]
      (g : Langlands.GeneralLinear n F.Carrier),
      μ.map (HaarModulus.normalizerConj (radical n F.Carrier)
        (Subgroup.inclusion leviSubgroup_le_normalizer (leviEquiv g))) =
        (T.determinantNorm n g : ℝ≥0)⁻¹ • μ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let : MeasurableSpace F.Carrier := borel _
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let : MeasurableSpace (radical n F.Carrier) := borel _
  let : BorelSpace (radical n F.Carrier) := ⟨rfl⟩
  intro μ hμ g
  let e : radical n F.Carrier ≃ₜ (Fin n → F.Carrier) :=
    { toEquiv :=
        { toFun := radicalCoordinates
          invFun := radicalElement
          left_inv := radicalElement_coordinates
          right_inv := radicalCoordinates_element }
      continuous_toFun := continuous_radicalCoordinates
      continuous_invFun := continuous_radicalElement }
  let c := HaarModulus.normalizerConj (radical n F.Carrier)
    (Subgroup.inclusion leviSubgroup_le_normalizer (leviEquiv g))
  have he : Measurable e := e.continuous.measurable
  have hc : Measurable c := c.continuous.measurable
  have hm : Measurable (Matrix.toLin' g.val) :=
    (LinearMap.continuous_on_pi _).measurable
  have : IsAddHaarMeasure (μ.map e) := radicalCoordinates_isAddHaar F T n μ
  have hχ (a : F.Carrier) (ha : a ≠ 0) :
      (addHaar : Measure F.Carrier).map (fun x => a * x) =
        (T.normalizedAbsHom a)⁻¹ • addHaar :=
    HarmonicAnalysis.padicScalarHaarScaling F T addHaar (Units.mk0 a ha)
  apply e.toMeasurableEquiv.measurableEmbedding.map_injective
  calc
    (μ.map c).map e = (μ.map e).map (Matrix.toLin' g.val) := by
      rw [Measure.map_map he hc, Measure.map_map hm he]
      congr 1
      funext u
      exact radicalCoordinates_leviConj g u
    _ = (T.determinantNorm n g : ℝ≥0)⁻¹ • μ.map e :=
      HarmonicAnalysis.haarMeasure_map_matrix addHaar T.normalizedAbsHom hχ
        (μ.map e) (GeneralLinear.determinant g).ne_zero
    _ = ((T.determinantNorm n g : ℝ≥0)⁻¹ • μ).map e :=
      (Measure.map_smul _ he.aemeasurable).symm

/-- The actual positive Haar character of the radical, pulled back to `GL_n`
through the Levi equivalence, is the determinant norm. -/
theorem leviRadical_haarCharacter (n : ℕ) :
    letI := T.topology
    letI := T.fieldT2
    letI := T.generalLinearTopologicalGroup (n + 1)
    letI := T.generalLinearLocallyCompactSpace (n + 1)
    letI := locallyCompactSpace (n := n) (F := F.Carrier)
    (HaarModulus.closedRestrictCharacter (radical n F.Carrier)
      radical_isClosed (leviSubgroup n F.Carrier) leviSubgroup_le_normalizer).comp
      (leviEquiv (n := n) (F := F.Carrier)).toMonoidHom = T.determinantNorm n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup (n + 1)
  let := T.generalLinearLocallyCompactSpace (n + 1)
  let := locallyCompactSpace (n := n) (F := F.Carrier)
  let : LocallyCompactSpace (radical n F.Carrier) :=
    (radical_isClosed (n := n) (F := F.Carrier)).locallyCompactSpace
  let : MeasurableSpace (radical n F.Carrier) := borel _
  let : BorelSpace (radical n F.Carrier) := ⟨rfl⟩
  apply MonoidHom.ext
  intro g
  apply Units.ext
  change mulEquivHaarChar
    (HaarModulus.normalizerConj (radical n F.Carrier)
      (Subgroup.inclusion leviSubgroup_le_normalizer (leviEquiv g))) =
    (T.determinantNorm n g : ℝ≥0)
  let μ : Measure (radical n F.Carrier) := haar
  have : IsHaarMeasure ((T.determinantNorm n g : ℝ≥0)⁻¹ • μ) :=
    IsHaarMeasure.nnreal_smul μ (inv_ne_zero (T.determinantNorm n g).ne_zero)
  rw [mulEquivHaarChar_eq μ]
  rw! [radicalHaar_map_leviConj F T n μ g]
  have h := mul_haarScalarFactor_smul μ μ
    (inv_ne_zero (T.determinantNorm n g).ne_zero)
  rw [haarScalarFactor_self] at h
  simpa only [inv_inv] using
    (Units.eq_inv_of_mul_eq_one_left (u := (T.determinantNorm n g)⁻¹)
      (by simpa only [Units.val_inv_eq_inv_val] using h))

end GeneralLinear.Mirabolic
end Langlands.AllFieldBZ
