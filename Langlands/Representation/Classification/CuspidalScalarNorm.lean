import Langlands.Representation.Classification.LanglandsQuotients
import Langlands.Representation.Classification.SegmentFullJacquetAssembly
import Langlands.Representation.Classification.SegmentConstituentCentralCharacterProof
import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof

/-! A scalar-uniformizer norm on cuspidal classes and its strict twist order. -/

noncomputable section

namespace Langlands.PadicField.TopologicalData.CuspidalDatum

open GeneralLinear Classification CategoryTheory

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- The scalar character of a cuspidal class, chosen on its canonical representative. -/
def scalarCharacter (ρ : CuspidalDatum.{uV, uF} T) : F.Carrierˣ →* ℂˣ :=
  (SegmentFullJacquet.exists_hasScalarCharacter F T ρ.representative).choose

theorem scalarCharacter_acts (ρ : CuspidalDatum.{uV, uF} T) :
    letI := T.topology
    HasScalarCharacter ρ.representative.obj.representation GeneralLinear.scalar ρ.scalarCharacter :=
  (SegmentFullJacquet.exists_hasScalarCharacter F T ρ.representative).choose_spec

/-- The chosen scalar character is the scalar character of any actual representative. -/
theorem scalarCharacter_eq_of_isRepresentedBy
    (ρ : CuspidalDatum.{uV, uF} T)
    (A : letI := T.topology;
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ.rank))
    (hA : ρ.IsRepresentedBy A) (ω : F.Carrierˣ →* ℂˣ)
    (hω : letI := T.topology;
      HasScalarCharacter A.obj.representation GeneralLinear.scalar ω) :
    ρ.scalarCharacter = ω := by
  let := T.topology
  obtain ⟨e⟩ := (SupercuspidalRep.isoClass_eq_iff ρ.representative A).mp
    (ρ.isRepresentedBy_representative.trans hA.symm)
  let E := SmoothRep.equivOfIso ((supercuspidalProperty (F := F.Carrier)
    (n := ρ.rank)).ι.mapIso e)
  have hω' := hω.of_injective E.toIntertwiningMap E.injective
  let := ρ.representative.property.1
  let : Nontrivial ρ.representative.obj := IsSimpleModule.nontrivial
    (MonoidAlgebra ℂ (GeneralLinear ρ.rank F.Carrier)) ρ.representative.obj.representation.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : ρ.representative.obj)
  apply MonoidHom.ext
  intro a
  apply Units.ext
  apply smul_left_injective ℂ hv
  exact (ρ.scalarCharacter_acts a v).symm.trans (hω' a v)

/-- The norm of the scalar uniformizer eigenvalue of a cuspidal class. -/
def scalarUniformizerNorm (ρ : CuspidalDatum.{uV, uF} T) : ℝ :=
  ‖(ρ.scalarCharacter (LocalFactor.PadicAbelian.uniformizerUnit T) : ℂ)‖

theorem scalarUniformizerNorm_pos (ρ : CuspidalDatum.{uV, uF} T) :
    0 < ρ.scalarUniformizerNorm :=
  norm_pos_iff.mpr (ρ.scalarCharacter (LocalFactor.PadicAbelian.uniformizerUnit T)).ne_zero

set_option maxHeartbeats 800000 in
/-- A real determinant twist multiplies the scalar norm by `q^(-rank*s)`. -/
theorem scalarUniformizerNorm_twist (ρ : CuspidalDatum.{uV, uF} T) (s : ℝ) :
    (ρ.twist s).scalarUniformizerNorm =
      ρ.scalarUniformizerNorm * (T.residueCardinality : ℝ) ^ (-(ρ.rank : ℝ) * s) := by
  let := T.topology
  let A := ρ.representative
  let At := SupercuspidalRep.twist (T.determinantPowerCharacter ρ.rank s)
    (T.isOpen_ker_determinantPowerCharacter ρ.rank s)
    (T.ker_determinant_le_ker_determinantPowerCharacter ρ.rank s) A
  have hAt : (ρ.twist s).IsRepresentedBy At := by
    change At.isoClass = T.supercuspidalClassRealPowerTwist ρ.rank s ρ.cls
    rw [← ρ.isRepresentedBy_representative]
    rfl
  have hω := scalarCharacter_eq_of_isRepresentedBy (ρ.twist s) At hAt
    (ρ.scalarCharacter * (T.determinantPowerCharacter ρ.rank s).comp GeneralLinear.scalar)
    (hasScalarCharacter_twist _ ρ.scalarCharacter_acts)
  unfold scalarUniformizerNorm
  rw [hω]
  simp only [MonoidHom.mul_apply, Units.val_mul, MonoidHom.comp_apply, norm_mul]
  rw [IntegralTwistFreeness.scalar_uniformizer_value]
  have hq : (0 : ℝ) < T.residueCardinality :=
    lt_trans zero_lt_one (by exact_mod_cast T.residueCardinality_gt_one)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hq _)]

/-- Increasing the real twist strictly decreases the scalar-uniformizer norm. -/
theorem strictAnti_scalarUniformizerNorm_twist (ρ : CuspidalDatum.{uV, uF} T) :
    StrictAnti (fun s : ℝ => (ρ.twist s).scalarUniformizerNorm) := by
  intro s t hst
  change (ρ.twist t).scalarUniformizerNorm < (ρ.twist s).scalarUniformizerNorm
  rw [scalarUniformizerNorm_twist, scalarUniformizerNorm_twist]
  apply mul_lt_mul_of_pos_left _ ρ.scalarUniformizerNorm_pos
  apply Real.rpow_lt_rpow_of_exponent_lt
  · exact_mod_cast T.residueCardinality_gt_one
  · have hr : (0 : ℝ) < ρ.rank := by exact_mod_cast ρ.rank_pos
    nlinarith

end Langlands.PadicField.TopologicalData.CuspidalDatum
