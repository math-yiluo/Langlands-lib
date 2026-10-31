import Langlands.Group.GL.MirabolicModularCharacterStatement
import Langlands.Group.GL.MirabolicModulusProof
import Langlands.Group.GL.MirabolicProjection
import Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity
import Langlands.Analysis.Local.ModularCompactAverage

noncomputable section

namespace Langlands

open MeasureTheory Measure Set TopologicalSpace
open scoped NNReal ENNReal

universe uF

namespace GeneralLinear.Mirabolic

section Algebra

variable {K : Type uF} [Field K] {n : ℕ}

private def radicalPart (g : mirabolic n K) : radical n K :=
  radicalElement (lastColumn g)

private theorem radicalPart_val (g : mirabolic n K) :
    (radicalPart g).val = g * (levi (projection g))⁻¹ := by
  have h := congrArg (fun q => q * (levi (projection g))⁻¹)
    (eq_radicalElement_mul_levi g)
  simpa only [radicalPart, mul_inv_cancel_right] using h.symm

private theorem projection_radical (u : radical n K) : projection u.val = 1 :=
  (projection_eq_one_iff u.val).mpr u.property

private theorem radicalPart_radical_mul (u : radical n K) (g : mirabolic n K) :
    radicalPart (u.val * g) = u * radicalPart g := by
  apply Subtype.ext
  simp only [radicalPart_val, map_mul, projection_radical, one_mul, Subgroup.coe_mul,
    mul_assoc]

private theorem projection_conj_of_commute (m : Langlands.GeneralLinear n K)
    (hm : ∀ m', m * m' = m' * m) (g : mirabolic n K) :
    projection ((levi m)⁻¹ * g * levi m) = projection g := by
  rw [map_mul, map_mul, map_inv, projection_levi, mul_assoc, ← hm, inv_mul_cancel_left]

private theorem character_radical (χ : mirabolic n K →* ℝ≥0) (u : radical n K) :
    χ u.val = 1 := by
  let z := levi (Matrix.GeneralLinearGroup.scalar (Fin n) (-1 : Kˣ))
  have hz : z * u.val * z⁻¹ = u.val⁻¹ := by
    obtain ⟨v, rfl⟩ := (radicalEquiv (n := n) (F := K)).symm.surjective u
    change levi _ * (radicalElement v.toAdd).val * (levi _)⁻¹ = _
    rw [levi_conjugate_radicalElement]
    have he : (Matrix.GeneralLinearGroup.scalar (Fin n) (-1 : Kˣ)).val.mulVec v.toAdd =
        -v.toAdd := by
      simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    rw [he]
    have hi : radicalElement (-v.toAdd) = (radicalElement v.toAdd)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← radicalElement_add, neg_add_cancel, radicalElement_zero]
    rw [hi, Subgroup.coe_inv]
    rfl
  have he : χ u.val = χ u.val⁻¹ := by
    have h := congrArg χ hz
    rw [map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel₀
      ((Group.isUnit z).map χ).ne_zero, one_mul] at h
    exact h
  have hp : χ u.val ^ 2 = 1 := by
    calc
      _ = χ u.val * χ u.val⁻¹ := by rw [← he, pow_two]
      _ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  exact (pow_eq_one_iff_of_nonneg (zero_le) (by decide : 2 ≠ 0)).mp hp

private theorem det_lastRow (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hA : ∀ j, A (Fin.last n) j = if j = Fin.last n then 1 else 0) :
    Matrix.det A = Matrix.det (A.submatrix Fin.castSucc Fin.castSucc) := by
  rw [Matrix.det_succ_row A (Fin.last n)]
  simp only [hA, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp [Fin.succAbove_last, ← two_mul, pow_mul]

private theorem determinant_projection (g : mirabolic n K) :
    GeneralLinear.determinant g.val = GeneralLinear.determinant (projection g) :=
  Units.ext (det_lastRow g.val.val g.property)

end Algebra

section Topology

variable {K : Type uF} [Field K] [TopologicalSpace K] [IsTopologicalRing K] {n : ℕ}

private def radicalConj (m : Langlands.GeneralLinear n K) : radical n K ≃ₜ* radical n K :=
  HaarModulus.normalizerConj (radical n K)
    (Subgroup.inclusion leviSubgroup_le_normalizer (leviEquiv m))

private theorem radicalPart_conj_of_commute (m : Langlands.GeneralLinear n K)
    (hm : ∀ m', m * m' = m' * m) (g : mirabolic n K) :
    radicalPart ((levi m)⁻¹ * g * levi m) = radicalConj m⁻¹ (radicalPart g) := by
  have hc : levi m * (levi (projection g))⁻¹ =
      (levi (projection g))⁻¹ * levi m := by
    rw [← map_inv, ← map_mul, ← map_mul, hm]
  apply Subtype.ext
  change (radicalPart _).val = levi m⁻¹ * (radicalPart g).val * (levi m⁻¹)⁻¹
  rw [radicalPart_val, radicalPart_val, projection_conj_of_commute m hm,
    map_inv, inv_inv, mul_assoc _ (levi m), hc]
  simp only [mul_assoc]

private def partsHomeomorph : mirabolic n K ≃ₜ radical n K × Langlands.GeneralLinear n K where
  toFun g := (radicalPart g, projection g)
  invFun p := p.1.val * levi p.2
  left_inv g := by
    change (radicalPart g).val * levi (projection g) = g
    rw [radicalPart_val, inv_mul_cancel_right]
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      simp only [radicalPart_val, map_mul, projection_radical, projection_levi, one_mul,
        mul_inv_cancel_right]
    · simp only [map_mul, projection_radical, projection_levi, one_mul]
  continuous_toFun :=
    (continuous_radicalElement.comp continuous_lastColumn).prodMk continuous_projection
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_fst).mul (continuous_levi.comp continuous_snd)

private theorem slice_eq_image (E : Set (radical n K)) (K' : Set (Langlands.GeneralLinear n K)) :
    projection ⁻¹' K' ∩ radicalPart ⁻¹' E =
      partsHomeomorph.symm '' (E ×ˢ K') := by
  rw [Homeomorph.image_symm]
  ext g
  exact and_comm

private theorem map_radicalPart_restrict_eq_smul [T2Space K]
    [LocallyCompactSpace (mirabolic n K)] [SecondCountableTopology (mirabolic n K)]
    [MeasurableSpace (mirabolic n K)] [BorelSpace (mirabolic n K)]
    [MeasurableSpace (radical n K)] [BorelSpace (radical n K)]
    (ν : Measure (mirabolic n K)) [IsHaarMeasure ν]
    (μ : Measure (radical n K)) [IsHaarMeasure μ]
    (C : Compacts (Langlands.GeneralLinear n K)) :
    ∃ c : ℝ≥0, (ν.restrict (projection ⁻¹' (C : Set (Langlands.GeneralLinear n K)))).map radicalPart = c • μ := by
  have : LocallyCompactSpace (radical n K) := radical_isClosed.locallyCompactSpace
  have : SecondCountableTopology (radical n K) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have hr : Continuous (radicalPart (n := n) (K := K)) :=
    continuous_radicalElement.comp continuous_lastColumn
  have hC : MeasurableSet (projection ⁻¹' (C : Set (Langlands.GeneralLinear n K))) :=
    (C.isCompact.isClosed.preimage continuous_projection).measurableSet
  have hinv (u : radical n K) :
      (fun g : mirabolic n K => u.val * g) ⁻¹' (projection ⁻¹' (C : Set (Langlands.GeneralLinear n K))) =
        projection ⁻¹' (C : Set (Langlands.GeneralLinear n K)) := by
    ext g
    simp only [mem_preimage, map_mul, projection_radical, one_mul]
  have : IsMulLeftInvariant ((ν.restrict (projection ⁻¹' (C : Set (Langlands.GeneralLinear n K)))).map radicalPart) := by
    constructor
    intro u
    rw [Measure.map_map (measurable_const_mul u) hr.measurable]
    have he : (fun v => u * v) ∘ radicalPart =
        radicalPart ∘ (fun g : mirabolic n K => u.val * g) := by
      funext g
      exact (radicalPart_radical_mul u g).symm
    rw [he, ← Measure.map_map hr.measurable (measurable_const_mul u.val)]
    congr 1
    have h := Measure.restrict_map (μ := ν) (measurable_const_mul u.val) hC
    rw [map_mul_left_eq_self, hinv u] at h
    exact h.symm
  have : IsFiniteMeasureOnCompacts
      ((ν.restrict (projection ⁻¹' (C : Set (Langlands.GeneralLinear n K)))).map radicalPart) := by
    refine ⟨fun E hE => ?_⟩
    rw [Measure.map_apply hr.measurable hE.measurableSet,
      Measure.restrict_apply (hr.measurable hE.measurableSet), inter_comm, slice_eq_image]
    exact ((hE.prod C.isCompact).image partsHomeomorph.symm.continuous).measure_lt_top
  exact ⟨_, isMulLeftInvariant_eq_smul _ μ⟩

private theorem modularCharacter_levi_of_commute [T2Space K]
    [LocallyCompactSpace (mirabolic n K)] [SecondCountableTopology (mirabolic n K)]
    [LocallyCompactSpace (Langlands.GeneralLinear n K)]
    (δ : Langlands.GeneralLinear n K →* ℝ≥0ˣ)
    (hδ : letI : MeasurableSpace (radical n K) := borel _
      ∀ (μ : Measure (radical n K)) [IsHaarMeasure μ] (m : Langlands.GeneralLinear n K),
        μ.map (radicalConj m) = (δ m : ℝ≥0)⁻¹ • μ)
    (m : Langlands.GeneralLinear n K) (hm : ∀ m', m * m' = m' * m) :
    modularCharacter (levi m) = (δ m : ℝ≥0) := by
  have : LocallyCompactSpace (radical n K) := radical_isClosed.locallyCompactSpace
  let : MeasurableSpace (mirabolic n K) := borel _
  let : BorelSpace (mirabolic n K) := ⟨rfl⟩
  let : MeasurableSpace (radical n K) := borel _
  let : BorelSpace (radical n K) := ⟨rfl⟩
  let ν : Measure (mirabolic n K) := haar
  let μ : Measure (radical n K) := haar
  let C : PositiveCompacts (Langlands.GeneralLinear n K) := Classical.choice inferInstance
  let U : PositiveCompacts (radical n K) := Classical.choice inferInstance
  let S : PositiveCompacts (mirabolic n K) :=
    (U ×ˢ C).map partsHomeomorph.symm partsHomeomorph.symm.continuous
      partsHomeomorph.symm.isOpenMap
  have hS : (S : Set (mirabolic n K)) =
      projection ⁻¹' (C : Set (Langlands.GeneralLinear n K)) ∩
        radicalPart ⁻¹' (U : Set (radical n K)) := by
    exact (slice_eq_image _ _).symm
  have hr : Continuous (radicalPart (n := n) (K := K)) :=
    continuous_radicalElement.comp continuous_lastColumn
  have ha : Continuous (radicalConj m⁻¹) := (radicalConj m⁻¹).continuous
  have hU : MeasurableSet (U : Set (radical n K)) := U.isCompact.measurableSet
  obtain ⟨c, hc⟩ := map_radicalPart_restrict_eq_smul ν μ C.toCompacts
  have hρ (E : Set (radical n K)) (hE : MeasurableSet E) :
      ν (projection ⁻¹' (C : Set (Langlands.GeneralLinear n K)) ∩ radicalPart ⁻¹' E) =
        c * μ E := by
    have h := congrArg (fun ρ : Measure (radical n K) => ρ E) hc
    simp only [Measure.smul_apply, nnreal_smul_coe_apply] at h
    rw [Measure.map_apply hr.measurable hE,
      Measure.restrict_apply (hr.measurable hE), inter_comm] at h
    exact h
  have e1 : ν S = c * μ U := by rw [hS, hρ _ hU]
  have hpre : (fun g : mirabolic n K => (levi m)⁻¹ * g * levi m) ⁻¹' (S : Set _) =
      projection ⁻¹' (C : Set (Langlands.GeneralLinear n K)) ∩
        radicalPart ⁻¹' ((radicalConj m⁻¹) ⁻¹' (U : Set (radical n K))) := by
    rw [hS]
    ext g
    simp only [mem_preimage, mem_inter_iff, projection_conj_of_commute m hm,
      radicalPart_conj_of_commute m hm]
  have e2 := ModularCompactAverage.measure_preimage_conj ν (levi m) S.isCompact.measurableSet
  rw [hpre, hρ _ (ha.measurable hU), ← Measure.map_apply ha.measurable hU, hδ μ m⁻¹,
    Measure.smul_apply, nnreal_smul_coe_apply, map_inv δ m, Units.val_inv_eq_inv_val,
    inv_inv, e1] at e2
  have hpos : (c : ℝ≥0∞) * μ U ≠ 0 := by
    rw [← e1]
    exact (measure_pos_of_nonempty_interior ν S.interior_nonempty).ne'
  have hfin : (c : ℝ≥0∞) * μ U ≠ ∞ := by
    rw [← e1]
    exact S.isCompact.measure_lt_top.ne
  have key : ((δ m : ℝ≥0) : ℝ≥0∞) * ((c : ℝ≥0∞) * μ U) =
      (modularCharacter (levi m) : ℝ≥0∞) * ((c : ℝ≥0∞) * μ U) := by
    rw [← e2]
    ring
  exact (ENNReal.coe_injective ((ENNReal.mul_left_inj hpos hfin).mp key)).symm

private theorem modularCharacter_levi [T2Space K]
    [LocallyCompactSpace (mirabolic n K)] [SecondCountableTopology (mirabolic n K)]
    [LocallyCompactSpace (Langlands.GeneralLinear n K)]
    (δ : Langlands.GeneralLinear n K →* ℝ≥0ˣ)
    (hδ : letI : MeasurableSpace (radical n K) := borel _
      ∀ (μ : Measure (radical n K)) [IsHaarMeasure μ] (m : Langlands.GeneralLinear n K),
        μ.map (radicalConj m) = (δ m : ℝ≥0)⁻¹ • μ)
    (m : Langlands.GeneralLinear n K) :
    modularCharacter (levi m) = (δ m : ℝ≥0) := by
  let χ : Langlands.GeneralLinear n K →* ℝ≥0 :=
    (modularCharacter.comp levi) * (Units.coeHom ℝ≥0).comp δ⁻¹
  have hχ (x : Langlands.GeneralLinear n K) :
      χ x = modularCharacter (levi x) * (δ x : ℝ≥0)⁻¹ := by
    simp only [χ, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply,
      Units.coeHom_apply, Units.val_inv_eq_inv_val]
  have hs (a : Kˣ) : χ (Matrix.GeneralLinearGroup.scalar (Fin n) a) = 1 := by
    rw [hχ, modularCharacter_levi_of_commute δ hδ _
      (fun m' => Matrix.GeneralLinearGroup.scalar_commute a m'),
      mul_inv_cancel₀ (Units.ne_zero _)]
  have h := RankinSelberg.GeneralLinearUnimodularity.character_eq_one χ hs m
  rwa [hχ, mul_inv_eq_one₀ (Units.ne_zero _)] at h

end Topology

end GeneralLinear.Mirabolic

open GeneralLinear.Mirabolic in
/-- Mathlib's Haar-defined modular character of the actual mirabolic subgroup
is the positive residue-normalized determinant norm. -/
theorem mirabolicModularCharacter {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) : MirabolicModularCharacterStatement.{uF} F T := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  intro n
  let := T.generalLinearTopologicalGroup (n + 1)
  let := T.generalLinearLocallyCompactSpace (n + 1)
  let := T.generalLinearLocallyCompactSpace n
  let := locallyCompactSpace (n := n) (F := F.Carrier)
  have : SecondCountableTopology (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) :=
    inferInstanceAs (SecondCountableTopology (Fin (n + 1) → Fin (n + 1) → F.Carrier))
  have : SecondCountableTopology (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  have : SecondCountableTopology (GeneralLinear (n + 1) F.Carrier) :=
    Units.isInducing_embedProduct.secondCountableTopology
  have : SecondCountableTopology (GeneralLinear.mirabolic n F.Carrier) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  intro g
  have hlevi (m : GeneralLinear n F.Carrier) :
      modularCharacter (levi m) = (T.determinantNorm n m : ℝ≥0) :=
    modularCharacter_levi (T.determinantNorm n) (radicalHaar_map_leviConj F T n) m
  have hdet : T.determinantNorm (n + 1) g.val = T.determinantNorm n (projection g) := by
    exact congrArg T.normalizedAbsUnits (determinant_projection g)
  calc
    modularCharacter g =
        modularCharacter ((radicalPart g).val * levi (projection g)) := by
      congr 1
      exact eq_radicalElement_mul_levi g
    _ = (T.determinantNorm n (projection g) : ℝ≥0) := by
      rw [map_mul, character_radical modularCharacter, one_mul, hlevi]
    _ = (T.determinantNorm (n + 1) g.val : ℝ≥0) := congrArg Units.val hdet.symm

end Langlands
