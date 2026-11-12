import Langlands.Representation.Aubert.GeneralLinearSpecialization
import Langlands.Group.GL.BlockModulusHaarProof
import Langlands.Representation.Parabolic.UnipotentFiniteContainment

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal

namespace Langlands.Parabolic

universe uF

/-- The actual Haar conjugation character on the entire upper block parabolic is
its explicit block modulus, in every rank and for every supplied p-adic topology. -/
theorem generalLinearModulusCompatibility {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) {n : ℕ}
    (B : GeneralLinear.BlockShape n) : GeneralLinearModulusCompatibility F T B := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  let := T.generalLinearNonarchimedean n
  let := (B.isClosed_unipotentSubgroup F.Carrier).locallyCompactSpace
  let : MeasurableSpace (B.unipotentSubgroup F.Carrier) := borel _
  let : BorelSpace (B.unipotentSubgroup F.Carrier) := ⟨rfl⟩
  let : MeasurableSpace (B.unipotentRadical F.Carrier) := borel _
  let : BorelSpace (B.unipotentRadical F.Carrier) := ⟨rfl⟩
  let e := B.unipotentRadicalAmbientEquiv F.Carrier
  let χ := HaarModulus.restrictCharacter (B.unipotentSubgroup F.Carrier)
    (B.parabolic F.Carrier) B.generalSemidirectDecomposition.le_normalizer
  have hrad (u : B.unipotentRadical F.Carrier) : χ u.val = 1 := by
    obtain ⟨K, hK, hu⟩ := unipotentFiniteContainment F T B {u}
    have huK : u ∈ K := hu u (Finset.mem_singleton_self u)
    let L := OpenSubgroup.comap e.symm.toMonoidHom e.symm.continuous K
    have hL : IsCompact (L : Set (B.unipotentSubgroup F.Carrier)) :=
      e.symm.toHomeomorph.isClosedEmbedding.isCompact_preimage hK
    have huL : e u ∈ L := by
      change e.symm (e u) ∈ K
      simpa using huK
    apply HaarModulus.normalizerCharacter_eq_one_of_preimage _ L hL
    ext v
    change e u * v * (e u)⁻¹ ∈ L ↔ v ∈ L
    exact (L.toSubgroup.mul_mem_cancel_right (L.inv_mem huL)).trans
      (L.toSubgroup.mul_mem_cancel_left huL)
  have hlevi (m : B.Levi F.Carrier) : χ (B.leviInParabolic F.Carrier m) =
      T.leviModulus B m := by
    let φ := HaarModulus.normalizerConj (B.unipotentSubgroup F.Carrier)
      ⟨(B.leviInParabolic F.Carrier m).val,
        B.generalSemidirectDecomposition.le_normalizer
          (B.leviInParabolic F.Carrier m).property⟩
    let μ : Measure (B.unipotentSubgroup F.Carrier) := haar
    let ν := μ.map e.symm
    have : ν.IsHaarMeasure := e.symm.isHaarMeasure_map μ
    have heμ : ν.map e = μ :=
      e.toHomeomorph.toMeasurableEquiv.map_map_symm
    have hc : e ∘ B.leviAction F.Carrier m = φ ∘ e := by
      funext u
      apply Subtype.ext
      rfl
    have ha : Measurable (B.leviAction F.Carrier m) :=
      ((B.continuous_leviAction F.Carrier).comp
        (continuous_const.prodMk continuous_id)).measurable
    have he : Measurable (e : B.unipotentRadical F.Carrier →
        B.unipotentSubgroup F.Carrier) := e.continuous.measurable
    have hφ : Measurable (φ : B.unipotentSubgroup F.Carrier →
        B.unipotentSubgroup F.Carrier) := φ.continuous.measurable
    have hscale : μ.map φ = ((T.leviModulus B m : ℝ≥0)⁻¹) • μ := by
      have h := congrArg (Measure.map e)
        (glBlockModulusHaar p F T n B ν m)
      rw [Measure.map_map he ha, hc,
        ← Measure.map_map hφ he, heμ,
        Measure.map_smul _ he.aemeasurable, heμ] at h
      exact h
    apply Units.ext
    change mulEquivHaarChar φ = (T.leviModulus B m : ℝ≥0)
    have hδ : (T.leviModulus B m : ℝ≥0) ≠ 0 := Units.ne_zero _
    have : (((T.leviModulus B m : ℝ≥0)⁻¹) • μ).IsHaarMeasure :=
      IsHaarMeasure.nnreal_smul μ (inv_ne_zero hδ)
    have hfactor := mul_haarScalarFactor_smul μ μ (inv_ne_zero hδ)
    rw [haarScalarFactor_self] at hfactor
    rw [mulEquivHaarChar_eq μ φ]
    rw! [hscale]
    calc
      haarScalarFactor μ (((T.leviModulus B m : ℝ≥0)⁻¹) • μ) =
          (T.leviModulus B m : ℝ≥0) *
            ((T.leviModulus B m : ℝ≥0)⁻¹ *
              haarScalarFactor μ (((T.leviModulus B m : ℝ≥0)⁻¹) • μ)) := by
                rw [← mul_assoc, mul_inv_cancel₀ hδ, one_mul]
      _ = (T.leviModulus B m : ℝ≥0) := by rw [hfactor, mul_one]
  change χ = (T.leviModulus B).comp (B.leviProjection F.Carrier)
  apply MonoidHom.ext
  intro g
  change χ g = T.leviModulus B (B.leviProjection F.Carrier g)
  have hg : (B.unipotentPart F.Carrier g).val *
      B.leviInParabolic F.Carrier (B.leviProjection F.Carrier g) = g :=
    (B.decomposition F.Carrier).left_inv g
  calc
    χ g = χ ((B.unipotentPart F.Carrier g).val *
        B.leviInParabolic F.Carrier (B.leviProjection F.Carrier g)) := congrArg χ hg.symm
    _ = T.leviModulus B (B.leviProjection F.Carrier g) := by
      rw [map_mul, hrad, hlevi, one_mul]

end Langlands.Parabolic
