import Langlands.Representation.Classification.LinkedSegmentHeadExponentStatement
import Langlands.Representation.Classification.UnitaryExponentScalarNormProof
import Langlands.Representation.Classification.SegmentConstituentCentralCharacterProof
import Langlands.Representation.Classification.SegmentLinkageOrientationProof
import Langlands.Representation.Classification.SegmentSupportContainment
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.LocalField.Uniformizer

/-!
# Linked-head exponent comparison

Both clauses follow from the segment scalar character, the public scalar-norm
theorem for each supplied positive form, and the linkage endpoint inequalities.
-/

namespace Langlands.Classification

open GeneralLinear
open scoped NNReal

universe uG uF uV

/-- Taking logarithms cancels the common scalar character and gives the
difference of the two arbitrary supplied exponents. -/
private theorem exponent_difference_of_norm_identities
    {c t u v : ℝ} (hc : 0 < c) (ht : 0 < t) (ht1 : t < 1)
    {r m n a b : ℕ} (hr : 0 < r) (hm : 0 < m) (hn : 0 < n)
    (h₁ : c ^ m * t ^ ((r : ℝ) * m * ((a : ℝ) + ((m : ℝ) - 1) / 2)) =
      t ^ ((r : ℝ) * m * u))
    (h₂ : c ^ n * t ^ ((r : ℝ) * n * ((b : ℝ) + ((n : ℝ) - 1) / 2)) =
      t ^ ((r : ℝ) * n * v)) :
    v - u = (b : ℝ) - a + ((n : ℝ) - m) / 2 := by
  have hlog₁ := congrArg Real.log h₁
  have hlog₂ := congrArg Real.log h₂
  rw [Real.log_mul (pow_pos hc _).ne' (Real.rpow_pos_of_pos ht _).ne',
    Real.log_pow, Real.log_rpow ht, Real.log_rpow ht] at hlog₁ hlog₂
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hm' : (m : ℝ) * (Real.log c +
      r * ((a : ℝ) + ((m : ℝ) - 1) / 2 - u) * Real.log t) = 0 := by
    nlinarith [hlog₁]
  have hn' : (n : ℝ) * (Real.log c +
      r * ((b : ℝ) + ((n : ℝ) - 1) / 2 - v) * Real.log t) = 0 := by
    nlinarith [hlog₂]
  have hmean₁ := (mul_eq_zero.mp hm').resolve_left hm0
  have hmean₂ := (mul_eq_zero.mp hn').resolve_left hn0
  have hdiff : ((r : ℝ) *
      (((a : ℝ) + ((m : ℝ) - 1) / 2 - u) -
        ((b : ℝ) + ((n : ℝ) - 1) / 2 - v))) * Real.log t = 0 := by
    nlinarith [hmean₁, hmean₂]
  have hlogne : Real.log t ≠ 0 := (Real.log_neg ht ht1).ne
  have hdiff' := (mul_eq_zero.mp hdiff).resolve_right hlogne
  have hmean := (mul_eq_zero.mp hdiff').resolve_left hr0
  linarith

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Adaptation of Worker 167's twisted representative and scalar calculation.
Here the arbitrary supplied positive form replaces analytic square-integrability. -/
private theorem segmentHead_norm_identity :
    letI := T.topology
    ∀ (ρ : T.CuspidalDatum.{uV, uF})
      (A : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ.rank))
      (_hA : A.isoClass = ρ.cls) (ω : F.Carrierˣ →* ℂˣ)
      (_hω : HasScalarCharacter A.obj.representation scalar ω)
      (Δ : T.Segment.{uV, uF}) (a : ℕ) (_hbase : Δ.base = ρ.twist (a : ℝ))
      (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
      T.IsSegmentHead Δ π →
      ∀ (u : UnitaryExponentData (T.determinantNorm Δ.degree) π.representation)
        (z : F.Carrierˣ),
        ‖(ω z : ℂ)‖ ^ Δ.length *
          T.normalizedAbs z ^
            ((ρ.rank : ℝ) * Δ.length * ((a : ℝ) + ((Δ.length : ℝ) - 1) / 2)) =
          T.normalizedAbs z ^ ((ρ.rank : ℝ) * Δ.length * u.exponent) := by
  let := T.topology
  intro ρ A hA ω hω Δ a hbase π hh u z
  obtain ⟨base, m, hm⟩ := Δ
  dsimp only at hbase
  subst base
  let Aa := SupercuspidalRep.twist (T.determinantPowerCharacter ρ.rank a)
    (T.isOpen_ker_determinantPowerCharacter ρ.rank a)
    (T.ker_determinant_le_ker_determinantPowerCharacter ρ.rank a) A
  let ωa := ω * (T.determinantPowerCharacter ρ.rank a).comp scalar
  have hAa : (ρ.twist (a : ℝ)).IsRepresentedBy Aa := by
    change Aa.isoClass = T.supercuspidalClassRealPowerTwist ρ.rank a ρ.cls
    rw [← hA]
    rfl
  have hωa : HasScalarCharacter Aa.obj.representation scalar ωa := by
    intro w v
    change A.obj at v
    change (T.determinantPowerCharacter ρ.rank a (scalar w) : ℂ) •
      A.obj.representation (scalar w) v =
      ((ω w : ℂ) * (T.determinantPowerCharacter ρ.rank a (scalar w) : ℂ)) • v
    rw [hω w v]
    simp only [smul_smul, mul_comm]
  let Δa : T.Segment.{uV, uF} := ⟨ρ.twist (a : ℝ), m, hm⟩
  have hscalar := (segmentConstituentCentralCharacter F T Δa ωa Aa hAa hωa).2.2 π
    (Or.inr hh.isSegmentQuotient)
  let : π.representation.IsIrreducible := hh.choose_spec.2.1
  let : Nontrivial π :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear Δa.degree F.Carrier))
      π.representation.asModule
  have hnorm' := unitaryExponentScalarNorm (GeneralLinear Δa.degree F.Carrier) π
    (T.determinantNorm Δa.degree) π.representation u (scalar z) _ (hscalar z)
  change ‖((ωa z : ℂ) ^ m *
    (T.determinantPowerCharacter (m * ρ.rank) (((m : ℝ) - 1) / 2)
      (scalar z) : ℂ))‖ = _ at hnorm'
  rw [norm_mul, norm_pow, T.norm_determinantPowerCharacter_scalar,
    T.determinantNorm_scalar] at hnorm'
  change ‖(ωa z : ℂ)‖ ^ m *
      T.normalizedAbs z ^ ((m * ρ.rank : ℕ) * (((m : ℝ) - 1) / 2)) =
    (T.normalizedAbs z ^ (m * ρ.rank)) ^ u.exponent at hnorm'
  rw [← Real.rpow_natCast_mul (T.normalizedAbs_nonneg _)] at hnorm'
  have hωnorm : ‖(ωa z : ℂ)‖ =
      ‖(ω z : ℂ)‖ * T.normalizedAbs z ^ ((ρ.rank : ℝ) * a) := by
    change ‖((ω z : ℂ) *
      (T.determinantPowerCharacter ρ.rank a (scalar z) : ℂ))‖ = _
    rw [norm_mul, T.norm_determinantPowerCharacter_scalar]
  rw [hωnorm, mul_pow, mul_assoc,
    ← Real.rpow_mul_natCast (T.normalizedAbs_nonneg _),
    ← Real.rpow_add (T.normalizedAbs_pos (Units.ne_zero z))] at hnorm'
  convert hnorm' using 2 <;> push_cast <;> ring

/-- Strict comparison. Noncontainment itself supplies
the endpoint bound, so integral twist freeness is not needed for this route. -/
private theorem exponent_lt_of_precedes :
    letI := T.topology
    ∀ (Δ Γ : T.Segment.{max uF uV, uF})
      (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
      (τ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Γ.degree F.Carrier)),
      T.IsSegmentHead Δ π → T.IsSegmentHead Γ τ →
      ∀ (u : UnitaryExponentData (T.determinantNorm Δ.degree) π.representation)
        (v : UnitaryExponentData (T.determinantNorm Γ.degree) τ.representation),
        Δ.Precedes Γ → u.exponent < v.exponent := by
  let := T.topology
  intro Δ Γ π τ hh hh' u v hp
  obtain ⟨k, hk, hbase⟩ := hp.2
  have hend : Δ.length < k + Γ.length := by
    by_contra h
    exact hp.1.2.1 (PadicField.TopologicalData.Segment.support_subset_of_base_shift hbase (by omega))
  obtain ⟨A, hA⟩ := Quotient.exists_rep Δ.base.cls
  have := T.generalLinearTopologicalGroup Δ.rank
  obtain ⟨χ, ⟨_, hχ⟩, _⟩ :=
    admissibleSchur_centralCharacter A.obj.representation A.property.2.1 A.property.1
  let ω : F.Carrierˣ →* ℂˣ := χ.comp scalarToCenter
  have hω : HasScalarCharacter A.obj.representation scalar ω := by
    intro z w
    exact hχ (scalarToCenter z) w
  let z := LocalFactor.PadicAbelian.uniformizerUnit T
  have hnorm₁ := segmentHead_norm_identity T Δ.base A hA ω hω Δ 0
    (by simp) π hh u z
  have hnorm₂ := segmentHead_norm_identity T Δ.base A hA ω hω Γ k
    hbase τ hh' v z
  have hc : 0 < ‖(ω z : ℂ)‖ := norm_pos_iff.mpr (Units.ne_zero _)
  have ht : 0 < T.normalizedAbs z := T.normalizedAbs_pos (Units.ne_zero z)
  have ht1 : T.normalizedAbs z < 1 := by
    change T.normalizedAbs T.uniformizer < 1
    rw [T.normalizedAbs_uniformizer, zpow_neg_one]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast T.residueCardinality_gt_one)
  have hdiff := exponent_difference_of_norm_identities hc ht ht1
    Δ.rank_pos Δ.length_pos Γ.length_pos hnorm₁ hnorm₂
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hend' : (Δ.length : ℝ) < k + Γ.length := by exact_mod_cast hend
  norm_num only [Nat.cast_zero, zero_add, sub_zero] at hdiff
  linarith

/-- The weak nonprecedence comparison and the strict precedence comparison
for all supplied unitary exponent witnesses of the actual strong heads. -/
theorem linkedSegmentHeadExponentComparison
    (F : PadicField.{uF} p) (T : F.TopologicalData) :
    LinkedSegmentHeadExponentComparison.{uF, uV} F T := by
  let := T.topology
  intro Δ Γ π τ hh hh' u v
  constructor
  · intro hlinked hnp
    have hreverse := hlinked.precedes_or_precedes.resolve_left hnp
    exact le_of_lt (exponent_lt_of_precedes T Γ Δ τ π hh' hh v u hreverse)
  · exact exponent_lt_of_precedes T Δ Γ π τ hh hh' u v

end Langlands.Classification
