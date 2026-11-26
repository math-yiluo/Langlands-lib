import Langlands.Representation.Aubert.GeneralLinearLocalFieldModulusStatement
import Langlands.AllField.Group.GL.BlockModulusHaarProof
import Langlands.AllField.Representation.Parabolic.UnipotentFiniteContainment

/-! # Haar conjugation on the full upper block parabolic

The Haar module of conjugation on the closed upper-block radical `U_B` of
`GL_n(F)`, for every element of the parabolic, is the residue-normalized
block modulus `T.leviModulus B` composed with the diagonal-block projection.
Radical elements have module one because they lie in compact open subgroups of
the radical. Block-diagonal elements have the explicit module by
`Langlands.AllField.glBlockModulusHaar`. A parabolic element is the product of
its radical part and the section of its diagonal-block projection.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal

namespace Langlands.Parabolic

universe u

/-- Over every nonarchimedean local field `LocalFieldData F`, every rank `n` and every
ordered block shape `B`, the Haar module of conjugation on the upper-block radical
equals `T.leviModulus B ∘ B.leviProjection F` on the whole parabolic. -/
theorem localFieldGeneralLinearModulusCompatibility :
    LocalFieldGeneralLinearModulusCompatibilityStatement.{u} := by
  intro F _ T n B
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearLocallyCompactSpace n
  let U := B.unipotentSubgroup F
  let P := B.parabolic F
  let h := B.generalSemidirectDecomposition (F := F)
  let : LocallyCompactSpace U := (B.isClosed_unipotentSubgroup F).locallyCompactSpace
  let : MeasurableSpace U := borel U
  let : BorelSpace U := ⟨rfl⟩
  let : MeasurableSpace (B.unipotentRadical F) := borel _
  let : BorelSpace (B.unipotentRadical F) := ⟨rfl⟩
  let e := B.unipotentRadicalAmbientEquiv F
  let χ := HaarModulus.restrictCharacter U P h.le_normalizer
  have hrad (u : B.unipotentRadical F) : χ u.val = 1 := by
    obtain ⟨K, hK, hu⟩ :=
      AllField.Parabolic.unipotentFiniteContainment F T B {u}
    let L := OpenSubgroup.comap e.symm.toMonoidHom e.symm.continuous K
    have hL : IsCompact (L : Set U) :=
      e.symm.toHomeomorph.isClosedEmbedding.isCompact_preimage hK
    have huL : e u ∈ L := by
      change e.symm (e u) ∈ K
      rw [e.symm_apply_apply]
      exact hu u (Finset.mem_singleton_self u)
    apply HaarModulus.normalizerCharacter_eq_one_of_preimage _ L hL
    ext v
    change e u * v * (e u)⁻¹ ∈ L ↔ v ∈ L
    exact (L.toSubgroup.mul_mem_cancel_right (L.inv_mem huL)).trans
      (L.toSubgroup.mul_mem_cancel_left huL)
  have hlevi (m : B.Levi F) :
      χ (B.leviInParabolic F m) = T.leviModulus B m := by
    let φ := HaarModulus.normalizerConj U
      ⟨(B.leviInParabolic F m).val, h.le_normalizer (B.leviInParabolic F m).property⟩
    let μ : Measure U := haar
    let ν := μ.map e.symm
    have : ν.IsHaarMeasure := e.symm.isHaarMeasure_map μ
    have heμ : ν.map e = μ :=
      e.toHomeomorph.toMeasurableEquiv.map_map_symm
    have hc : e ∘ B.leviAction F m = φ ∘ e := by
      funext u
      apply Subtype.ext
      rfl
    have haction : Measurable (B.leviAction F m) :=
      ((B.continuous_leviAction F).comp
        (continuous_const.prodMk continuous_id)).measurable
    have he : Measurable (e : B.unipotentRadical F → U) := e.continuous.measurable
    have hφ : Measurable (φ : U → U) := φ.continuous.measurable
    have hm := congrArg (Measure.map e) (AllField.glBlockModulusHaar F T n B ν m)
    rw [Measure.map_map he haction, hc, ← Measure.map_map hφ he, heμ,
      Measure.map_smul _ he.aemeasurable, heμ] at hm
    apply Units.ext
    change mulEquivHaarChar φ = (T.leviModulus B m : ℝ≥0)
    let c : ℝ≥0 := T.leviModulus B m
    have hc₀ : c ≠ 0 := Units.ne_zero _
    have : (c⁻¹ • μ).IsHaarMeasure := IsHaarMeasure.nnreal_smul μ (inv_ne_zero hc₀)
    have hscale := mul_haarScalarFactor_smul μ μ (inv_ne_zero hc₀)
    rw [haarScalarFactor_self] at hscale
    rw [mulEquivHaarChar_eq μ φ]
    rw! [hm]
    change haarScalarFactor μ (c⁻¹ • μ) = c
    calc
      haarScalarFactor μ (c⁻¹ • μ) = c * (c⁻¹ * haarScalarFactor μ (c⁻¹ • μ)) := by
        rw [← mul_assoc, mul_inv_cancel₀ hc₀, one_mul]
      _ = c := by rw [hscale, mul_one]
  change χ = (T.leviModulus B).comp (B.leviProjection F)
  apply MonoidHom.ext
  intro g
  change χ g = T.leviModulus B (B.leviProjection F g)
  have hg : (B.unipotentPart F g).val *
      B.leviInParabolic F (B.leviProjection F g) = g :=
    (B.decomposition F).left_inv g
  calc
    χ g = χ ((B.unipotentPart F g).val * B.leviInParabolic F (B.leviProjection F g)) :=
      congrArg χ hg.symm
    _ = T.leviModulus B (B.leviProjection F g) := by rw [map_mul, hrad, hlevi, one_mul]

end Langlands.Parabolic
