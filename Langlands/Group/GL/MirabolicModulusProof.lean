import Langlands.Group.GL.MirabolicModulusStatement
import Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof

/-!
# Proof of the Haar modulus of the actual mirabolic radical

Actual radical Haar measure is transported to additive Haar measure in
last-column coordinates, where Levi conjugation is matrix-vector
multiplication. The published scalar and matrix Haar scaling theorems then
identify the positive Haar character with the residue-normalized determinant
norm, first on the Levi subgroup and then on the embedded smaller mirabolic
subgroup.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal

namespace Langlands

universe uF

/-- The multiplicative type synonym carries the measurable structure of the
underlying type. -/
local instance multiplicativeMeasurableSpace {A : Type*} [MeasurableSpace A] :
    MeasurableSpace (Multiplicative A) := ‹MeasurableSpace A›

local instance multiplicativeBorelSpace {A : Type*} [TopologicalSpace A]
    [MeasurableSpace A] [BorelSpace A] : BorelSpace (Multiplicative A) :=
  ‹BorelSpace A›

/-- A Haar measure on `Multiplicative A` is an additive Haar measure on `A`. -/
private theorem multiplicativeHaar_isAddHaar
    {A : Type*} [AddGroup A] [TopologicalSpace A] [MeasurableSpace A]
    (μ : Measure (Multiplicative A)) [IsHaarMeasure μ] :
    IsAddHaarMeasure (show Measure A from μ) where
  toIsFiniteMeasureOnCompacts := (inferInstance : IsFiniteMeasureOnCompacts μ)
  toIsOpenPosMeasure := (inferInstance : IsOpenPosMeasure μ)
  map_add_left_eq_self g := map_mul_left_eq_self μ (Multiplicative.ofAdd g)

namespace GeneralLinear.Mirabolic

section Coordinates

variable {K : Type*} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    {n : ℕ}

/-- The actual normalizer automorphism of `diag(g, 1)` acts by `g` in
last-column coordinates. -/
theorem radicalCoordinates_leviConj (g : Langlands.GeneralLinear n K)
    (u : radical n K) :
    radicalCoordinates
      (HaarModulus.normalizerConj (radical n K)
        (Subgroup.inclusion leviSubgroup_le_normalizer (leviEquiv g)) u) =
      g.val.mulVec (radicalCoordinates u) := by
  have h :
      HaarModulus.normalizerConj (radical n K)
        (Subgroup.inclusion leviSubgroup_le_normalizer (leviEquiv g)) u =
      radicalElement (g.val.mulVec (radicalCoordinates u)) := by
    apply Subtype.ext
    change levi g * u.val * (levi g)⁻¹ = _
    have h := levi_conjugate_radicalElement g (radicalCoordinates u)
    rw [radicalElement_coordinates] at h
    exact h
  rw [h, radicalCoordinates_element]

end Coordinates

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

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

/-- The actual positive Haar character of the rank `n + 1` radical, pulled back
to `P_n` through the successor equivalence, is the rank `n + 1` determinant
norm restricted to `P_n`. -/
theorem successorRadical_haarCharacter (n : ℕ) :
    letI := T.topology
    letI := T.fieldT2
    letI := T.generalLinearTopologicalGroup (n + 1 + 1)
    letI := T.generalLinearLocallyCompactSpace (n + 1 + 1)
    letI := locallyCompactSpace (n := n + 1) (F := F.Carrier)
    (HaarModulus.closedRestrictCharacter (radical (n + 1) F.Carrier)
      radical_isClosed (successorSubgroup n F.Carrier)
      successorSubgroup_le_normalizer).comp
      (successorEquiv (n := n) (F := F.Carrier)).toMonoidHom =
      (T.determinantNorm (n + 1)).comp
        (GeneralLinear.mirabolic n F.Carrier).subtype := by
  let := T.topology
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup (n + 1 + 1)
  let := T.generalLinearLocallyCompactSpace (n + 1 + 1)
  let := locallyCompactSpace (n := n + 1) (F := F.Carrier)
  apply MonoidHom.ext
  intro g
  exact congrArg (fun χ => χ g.val) (leviRadical_haarCharacter F T (n + 1))

end GeneralLinear.Mirabolic

open GeneralLinear.Mirabolic in
/-- The exact published mirabolic radical Haar-modulus proposition. -/
theorem mirabolicRadicalHaarModulus {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) : MirabolicRadicalHaarModulusStatement.{uF} F T := by
  let := T.topology
  let := T.fieldT2
  intro n
  exact ⟨leviRadical_haarCharacter F T n, successorRadical_haarCharacter F T n⟩

end Langlands
