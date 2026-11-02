import Langlands.Representation.Classification.IntegralSegmentHeadScalarNormStatement
import Langlands.Representation.Classification.SegmentConstituentCentralCharacterProof
import Langlands.Representation.Classification.ProductLeviCentralCharacter
import Langlands.Representation.Exponents.RealPartExistence
import Langlands.Representation.Smooth.Schur.Proof

/-! # A common scalar norm parameter for integral segment heads -/

noncomputable section

namespace Langlands.Classification

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Derive the common parameter from an actual supercuspidal representative
and transport its scalar action through the segment quotient. -/
theorem integralSegmentHeadScalarNorm :
    IntegralSegmentHeadScalarNorm.{uF, uV} F T := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro ρ
  obtain ⟨A, hA⟩ := Quotient.exists_rep ρ.cls
  have := T.generalLinearTopologicalGroup ρ.rank
  obtain ⟨χ, ⟨_, hχ⟩, _⟩ :=
    admissibleSchur_centralCharacter A.obj.representation A.property.2.1 A.property.1
  let ω : F.Carrierˣ →* ℂˣ := χ.comp scalarToCenter
  have hω : HasScalarCharacter A.obj.representation scalar ω :=
    fun z v => hχ (scalarToCenter z) v
  let : A.obj.representation.IsIrreducible := A.property.1
  let : Nontrivial A.obj :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear ρ.rank F.Carrier))
      A.obj.representation.asModule
  have hopen := hω.isOpen_ker GeneralLinear.scalarContinuous.continuous A.obj.isSmooth
  let s : ℝ := -Real.logb T.residueCardinality ‖(ω T.uniformizerUnit : ℂ)‖
  let t : ℝ := s / ρ.rank
  have hnorm (z : F.Carrierˣ) :
      ‖(ω z : ℂ)‖ = T.normalizedAbs z ^ s :=
    T.norm_eq_normalizedAbs_rpow_of_isOpen_ker ω hopen z
  refine ⟨t, ?_⟩
  intro Δ b a hcoord π hhead
  obtain ⟨base, m, hm⟩ := Δ
  rcases hcoord with ⟨hbase, ha⟩
  dsimp only at hbase ha
  subst base
  let Ab := SupercuspidalRep.twist (T.determinantPowerCharacter ρ.rank b)
    (T.isOpen_ker_determinantPowerCharacter ρ.rank b)
    (T.ker_determinant_le_ker_determinantPowerCharacter ρ.rank b) A
  let ωb : F.Carrierˣ →* ℂˣ :=
    ω * (T.determinantPowerCharacter ρ.rank b).comp scalar
  have hAb : (ρ.twist (b : ℝ)).IsRepresentedBy Ab := by
    change Ab.isoClass = T.supercuspidalClassRealPowerTwist ρ.rank b ρ.cls
    rw [← hA]
    rfl
  have hωb : HasScalarCharacter Ab.obj.representation scalar ωb :=
    T.hasScalarCharacter_segmentFactor A.obj (b : ℝ) hω
  let Δb : T.Segment.{max uF uV, uF} := ⟨ρ.twist (b : ℝ), m, hm⟩
  have hc := (segmentConstituentCentralCharacter F T Δb ωb Ab hAb hωb).2.2 π
    (Or.inr hhead.isSegmentQuotient)
  refine ⟨ωb ^ m *
    (T.determinantPowerCharacter (m * ρ.rank) (((m : ℝ) - 1) / 2)).comp scalar,
    hc, ?_⟩
  intro z
  have hpos : 0 < T.normalizedAbs z := T.normalizedAbs_pos z.ne_zero
  have hωbnorm : ‖(ωb z : ℂ)‖ =
      T.normalizedAbs z ^ (s + (ρ.rank : ℝ) * b) := by
    change ‖((ω z : ℂ) *
      (T.determinantPowerCharacter ρ.rank b (scalar z) : ℂ))‖ = _
    rw [norm_mul, hnorm, T.norm_determinantPowerCharacter_scalar, Real.rpow_add hpos]
  change ‖((ωb z : ℂ) ^ m *
    (T.determinantPowerCharacter (m * ρ.rank) (((m : ℝ) - 1) / 2)
      (scalar z) : ℂ))‖ = _
  rw [norm_mul, norm_pow, hωbnorm, T.norm_determinantPowerCharacter_scalar,
    ← Real.rpow_mul_natCast hpos.le, ← Real.rpow_add hpos]
  congr 1
  have ha' : (a : ℝ) = (b : ℝ) + (m : ℝ) - 1 := by exact_mod_cast ha
  have hr : (ρ.rank : ℝ) ≠ 0 := by exact_mod_cast ρ.rank_pos.ne'
  change (s + (ρ.rank : ℝ) * b) * m +
      (m * ρ.rank : ℕ) * (((m : ℝ) - 1) / 2) =
    (m * ρ.rank : ℕ) * (t + ((a : ℝ) + (b : ℝ)) / 2)
  rw [ha']
  push_cast
  dsimp only [t]
  field_simp
  ring

end Langlands.Classification
