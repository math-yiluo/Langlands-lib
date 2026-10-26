import Langlands.Representation.Classification.SquareIntegrableSegmentNonlinkageStatement
import Langlands.Representation.Classification.SegmentConstituentCentralCharacterProof
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.LocalField.Uniformizer

/-!
# Nonlinkage from unitary scalar actions

The scalar actions of the supplied square-integrable heads force equal
midpoints in any common twist string. Their supports are therefore nested,
contradicting the noncontainment clauses of linkage.
-/

namespace Langlands.PadicField.TopologicalData.Segment

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  {T : F.TopologicalData}

/-- If the base of the second segment starts `k` positions into the first and
its last index stays inside the first, its support is contained in the first. -/
theorem support_subset_of_base_shift {Δ Δ' : T.Segment.{uV, uF}} {k : ℕ}
    (hbase : Δ'.base = Δ.base.twist (k : ℝ))
    (hend : k + Δ'.length ≤ Δ.length) : Δ'.support ⊆ Δ.support := by
  rintro ρ ⟨i, hi, rfl⟩
  refine ⟨k + i, by omega, ?_⟩
  simp only [member, hbase, CuspidalDatum.twist_twist, Nat.cast_add]
  rw [add_comm]

/-- Segments in one integer twist string with equal midpoints have nested
supports. No injectivity or nonperiodicity of the twist action is needed. -/
theorem support_nested_of_equal_midpoint {ρ : T.CuspidalDatum.{uV, uF}}
    {Δ Δ' : T.Segment.{uV, uF}} {a b : ℕ}
    (hbase : Δ.base = ρ.twist (a : ℝ))
    (hbase' : Δ'.base = ρ.twist (b : ℝ))
    (hmid : 2 * a + Δ.length = 2 * b + Δ'.length) :
    Δ.support ⊆ Δ'.support ∨ Δ'.support ⊆ Δ.support := by
  rcases le_total a b with hab | hba
  · right
    apply support_subset_of_base_shift (k := b - a)
    · rw [hbase, hbase', CuspidalDatum.twist_twist]
      congr 1
      exact_mod_cast (show b = b - a + a by omega)
    · omega
  · left
    apply support_subset_of_base_shift (k := a - b)
    · rw [hbase, hbase', CuspidalDatum.twist_twist]
      congr 1
      exact_mod_cast (show a = a - b + b by omega)
    · omega

/-- Equal midpoint positions in a common twist string contradict linkage. -/
theorem not_isLinked_of_equal_midpoint {ρ : T.CuspidalDatum.{uV, uF}}
    {Δ Δ' : T.Segment.{uV, uF}} {a b : ℕ}
    (hbase : Δ.base = ρ.twist (a : ℝ))
    (hbase' : Δ'.base = ρ.twist (b : ℝ))
    (hmid : 2 * a + Δ.length = 2 * b + Δ'.length) : ¬ Δ.IsLinked Δ' := by
  intro h
  rcases support_nested_of_equal_midpoint hbase hbase' hmid with hsub | hsub
  · exact h.1 hsub
  · exact h.2.1 hsub

end Langlands.PadicField.TopologicalData.Segment


namespace Langlands.Classification

open GeneralLinear

universe uF uV

/-- The logarithms of two unit-norm segment scalar actions determine the same
midpoint even when the segment lengths differ. -/
private theorem midpoint_eq_of_norm_identities {c t : ℝ} (hc : 0 < c)
    (ht : 0 < t) (ht1 : t < 1) {r m n a b : ℕ}
    (hr : 0 < r) (hm : 0 < m) (hn : 0 < n)
    (h₁ : c ^ m * t ^ ((r : ℝ) * m * ((a : ℝ) + ((m : ℝ) - 1) / 2)) = 1)
    (h₂ : c ^ n * t ^ ((r : ℝ) * n * ((b : ℝ) + ((n : ℝ) - 1) / 2)) = 1) :
    2 * a + m = 2 * b + n := by
  have hlog₁ := congrArg Real.log h₁
  have hlog₂ := congrArg Real.log h₂
  rw [Real.log_mul (pow_pos hc _).ne' (Real.rpow_pos_of_pos ht _).ne',
    Real.log_pow, Real.log_rpow ht, Real.log_one] at hlog₁ hlog₂
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hm' : (m : ℝ) * (Real.log c + r * ((a : ℝ) + ((m : ℝ) - 1) / 2) *
      Real.log t) = 0 := by nlinarith [hlog₁]
  have hn' : (n : ℝ) * (Real.log c + r * ((b : ℝ) + ((n : ℝ) - 1) / 2) *
      Real.log t) = 0 := by nlinarith [hlog₂]
  have hmean₁ := (mul_eq_zero.mp hm').resolve_left hm0
  have hmean₂ := (mul_eq_zero.mp hn').resolve_left hn0
  have hdiff : ((r : ℝ) * (((a : ℝ) + ((m : ℝ) - 1) / 2) -
      ((b : ℝ) + ((n : ℝ) - 1) / 2))) * Real.log t = 0 := by
    nlinarith [hmean₁, hmean₂]
  have hlogne : Real.log t ≠ 0 := (Real.log_neg ht ht1).ne
  have hdiff' := (mul_eq_zero.mp hdiff).resolve_right hlogne
  have hmean := (mul_eq_zero.mp hdiff').resolve_left hr0
  have heq : (2 : ℝ) * a + m = 2 * b + n := by linarith
  exact_mod_cast heq

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Any prescribed scalar character of a nonzero square-integrable
representation has norm one on actual scalar matrices. -/
private theorem scalarCharacter_norm_eq_one {n : ℕ} {V : Type uV}
    [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear n F.Carrier) V)
    (hi : π.IsIrreducible) (hs : T.IsSquareIntegrable π)
    (ω : F.Carrierˣ →* ℂˣ) (hω : HasScalarCharacter π scalar ω)
    (z : F.Carrierˣ) : ‖(ω z : ℂ)‖ = 1 := by
  let := T.topology
  have := T.generalLinearTopologicalGroup n
  let := T.centralQuotientMeasurableSpace n
  have := T.centralQuotientBorelSpace n
  obtain ⟨μ, hμ⟩ := T.exists_isHaarMeasure_centralQuotient n
  obtain ⟨c, _⟩ := (hs μ).2
  let := hi
  have hn : Nontrivial V :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear n F.Carrier)) π.asModule
  let := hn
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have heq : (ω z : ℂ) = (c.character (scalarToCenter z) : ℂ) := by
    apply smul_left_injective ℂ hv
    exact (hω z v).symm.trans (c.acts (scalarToCenter z) v)
  rw [heq, c.norm_eq_one]

/-- The norm of a real determinant power on a scalar matrix retains the rank
factor in its exponent. -/
private theorem norm_determinantPowerCharacter_scalar (n : ℕ) (s : ℝ)
    (z : F.Carrierˣ) :
    ‖(T.determinantPowerCharacter n s (scalar z) : ℂ)‖ =
      T.normalizedAbs z ^ ((n : ℝ) * s) := by
  rw [coe_realPowerCharacter, T.determinantNorm_scalar]
  change ‖(((T.normalizedAbs z ^ n) ^ s : ℝ) : ℂ)‖ = _
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (pow_nonneg (T.normalizedAbs_nonneg _) _) _),
    ← Real.rpow_natCast_mul (T.normalizedAbs_nonneg _)]

/-- The segment scalar formula, if supplied, gives the exact norm identity for
any head whose base lies at a specified position in a common twist string. -/
private theorem segmentHead_norm_identity
    (hcentral : SegmentConstituentCentralCharacter.{uF, uV} F T) :
    letI := T.topology
    ∀ (ρ : T.CuspidalDatum.{uV, uF})
      (A : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ.rank))
      (_hA : A.isoClass = ρ.cls) (ω : F.Carrierˣ →* ℂˣ)
      (_hω : HasScalarCharacter A.obj.representation scalar ω)
      (Δ : T.Segment.{uV, uF}) (a : ℕ) (_hbase : Δ.base = ρ.twist (a : ℝ))
      (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
      T.IsSegmentHead Δ π → T.IsSquareIntegrable π.representation →
      ∀ z : F.Carrierˣ,
        ‖(ω z : ℂ)‖ ^ Δ.length *
          T.normalizedAbs z ^
            ((ρ.rank : ℝ) * Δ.length * ((a : ℝ) + ((Δ.length : ℝ) - 1) / 2)) = 1 := by
  let := T.topology
  intro ρ A hA ω hω Δ a hbase π hh hs z
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
  have hscalar := (hcentral Δa ωa Aa hAa hωa).2.2 π
    (Or.inr hh.isSegmentQuotient)
  have hi : π.representation.IsIrreducible := hh.choose_spec.2.1
  have hnorm := scalarCharacter_norm_eq_one T π.representation hi hs _ hscalar z
  change ‖((ωa z : ℂ) ^ m *
    (T.determinantPowerCharacter (m * ρ.rank) (((m : ℝ) - 1) / 2)
      (scalar z) : ℂ))‖ = 1 at hnorm
  rw [norm_mul, norm_pow, norm_determinantPowerCharacter_scalar] at hnorm
  have hωnorm : ‖(ωa z : ℂ)‖ =
      ‖(ω z : ℂ)‖ * T.normalizedAbs z ^ ((ρ.rank : ℝ) * a) := by
    change ‖((ω z : ℂ) *
      (T.determinantPowerCharacter ρ.rank a (scalar z) : ℂ))‖ = _
    rw [norm_mul, norm_determinantPowerCharacter_scalar]
  rw [hωnorm, mul_pow, mul_assoc,
    ← Real.rpow_mul_natCast (T.normalizedAbs_nonneg _),
    ← Real.rpow_add (T.normalizedAbs_pos (Units.ne_zero z))] at hnorm
  convert hnorm using 2
  congr 1
  push_cast
  ring

/-- Assemble nonlinkage from the scalar-character formula for constituents. -/
theorem squareIntegrableSegmentNonlinkage_of_centralCharacter
    (hcentral : SegmentConstituentCentralCharacter.{uF, max uF uV} F T) :
    SquareIntegrableSegmentNonlinkage.{uF, uV} F T := by
  let := T.topology
  intro Δ Δ' π π' hh hh' hs hs' hlinked
  obtain ⟨Γ, hΓ⟩ := hlinked.2.2
  have hbase : Δ.base ∈ Γ.support := by
    rw [hΓ]
    exact Or.inl Δ.base_mem_support
  have hbase' : Δ'.base ∈ Γ.support := by
    rw [hΓ]
    exact Or.inr Δ'.base_mem_support
  obtain ⟨a, _, ha⟩ := hbase
  obtain ⟨b, _, hb⟩ := hbase'
  have ha' : Δ.base = Γ.base.twist (a : ℝ) := ha.symm
  have hb' : Δ'.base = Γ.base.twist (b : ℝ) := hb.symm
  obtain ⟨A, hA⟩ := Quotient.exists_rep Γ.base.cls
  have := T.generalLinearTopologicalGroup Γ.rank
  obtain ⟨χ, ⟨_, hχ⟩, _⟩ :=
    admissibleSchur_centralCharacter A.obj.representation A.property.2.1 A.property.1
  let ω : F.Carrierˣ →* ℂˣ := χ.comp scalarToCenter
  have hω : HasScalarCharacter A.obj.representation scalar ω := by
    intro z v
    exact hχ (scalarToCenter z) v
  let z := LocalFactor.PadicAbelian.uniformizerUnit T
  have hnorm := segmentHead_norm_identity T hcentral Γ.base A hA ω hω Δ a ha' π hh hs z
  have hnorm' := segmentHead_norm_identity T hcentral Γ.base A hA ω hω Δ' b hb' π' hh' hs' z
  have hc : 0 < ‖(ω z : ℂ)‖ := norm_pos_iff.mpr (Units.ne_zero _)
  have ht : 0 < T.normalizedAbs z := T.normalizedAbs_pos (Units.ne_zero z)
  have ht1 : T.normalizedAbs z < 1 := by
    change T.normalizedAbs T.uniformizer < 1
    rw [T.normalizedAbs_uniformizer, zpow_neg_one]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast T.residueCardinality_gt_one)
  have hmid := midpoint_eq_of_norm_identities hc ht ht1 Γ.rank_pos
    Δ.length_pos Δ'.length_pos hnorm hnorm'
  exact PadicField.TopologicalData.Segment.not_isLinked_of_equal_midpoint ha' hb' hmid hlinked

/-- Segments with analytically square-integrable special heads are unlinked. -/
theorem squareIntegrableSegmentNonlinkage :
    SquareIntegrableSegmentNonlinkage.{uF, uV} F T :=
  squareIntegrableSegmentNonlinkage_of_centralCharacter T
    (segmentConstituentCentralCharacter.{uF, max uF uV} F T)

end Langlands.Classification
