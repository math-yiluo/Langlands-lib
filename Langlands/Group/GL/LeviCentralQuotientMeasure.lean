import Langlands.Group.GL.CentralQuotientMeasure

/-!
# Haar measure on the full central quotient of a standard block Levi

Positive characters of the central quotient of `∏ i, GL_(n_i)(F)` are trivial.
Hence every Haar measure on the actual central quotient of an actual p-adic
block Levi is right invariant and invariant under inversion.
-/

noncomputable section

namespace Langlands

open Matrix MeasureTheory
open scoped NNReal ENNReal

universe uG uF

/-- A right-invariant regular Haar measure on a locally compact group is
invariant under inversion. -/
theorem isInvInvariant_of_isMulRightInvariant
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] [μ.IsMulRightInvariant] :
    μ.IsInvInvariant := by
  constructor
  let c : ℝ≥0∞ := Measure.haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := Measure.isMulLeftInvariant_eq_smul_of_regular μ.inv μ
  have h2 : Measure.map Inv.inv (Measure.map Inv.inv μ) = c ^ 2 • μ := by
    rw [← Measure.inv_def μ, hc, Measure.map_smul _ (by fun_prop), ← Measure.inv_def μ, hc,
      smul_smul, pow_two]
  have μeq : μ = c ^ 2 • μ := by
    rw [Measure.map_map continuous_inv.measurable continuous_inv.measurable] at h2
    simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id] using h2
  have K : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  have hK : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [μeq]
    simp
  have hc2 : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj (Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
          K.isCompact.measure_lt_top.ne).1 hK
  have hc1 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective hc2
  rw [hc, hc1, one_smul]

namespace GeneralLinear.BlockShape

variable {F : Type uF} [Field F] {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- The full central quotient of a block Levi has no nontrivial
nonnegative-real characters. -/
theorem leviCentralQuotient_positiveCharacter_eq_one
    (χ : (B.Levi F ⧸ Subgroup.center (B.Levi F)) →* ℝ≥0)
    (q : B.Levi F ⧸ Subgroup.center (B.Levi F)) : χ q = 1 := by
  classical
  induction q using Quotient.inductionOn with
  | _ g =>
    have h : χ.comp (QuotientGroup.mk' (Subgroup.center (B.Levi F))) = 1 := by
      apply MonoidHom.pi_ext
      intro i x
      rw [MonoidHom.one_apply]
      let ψ : GeneralLinear (B.size i) F →* ℝ≥0 :=
        (χ.comp (QuotientGroup.mk' (Subgroup.center (B.Levi F)))).comp
          (MonoidHom.mulSingle (fun j => GeneralLinear (B.size j) F) i)
      refine RankinSelberg.GeneralLinearUnimodularity.character_eq_one ψ ?_ x
      intro a
      have ha : (Pi.mulSingle i (GeneralLinearGroup.scalar (Fin (B.size i)) a) : B.Levi F) ∈
          Subgroup.center (B.Levi F) := by
        rw [Subgroup.mem_center_iff]
        intro y
        funext j
        simp only [Pi.mul_apply]
        by_cases hj : j = i
        · subst hj
          simp only [Pi.mulSingle_eq_same]
          exact (GeneralLinearGroup.scalar_commute a (y j)).symm
        · simp only [Pi.mulSingle_eq_of_ne hj, mul_one, one_mul]
      change χ (QuotientGroup.mk
        (Pi.mulSingle i (GeneralLinearGroup.scalar (Fin (B.size i)) a) : B.Levi F)) = 1
      rw [(QuotientGroup.eq_one_iff _).mpr ha, map_one]
    exact DFunLike.congr_fun h g

variable [TopologicalSpace (B.Levi F)] [IsTopologicalGroup (B.Levi F)]
  [LocallyCompactSpace (B.Levi F ⧸ Subgroup.center (B.Levi F))]
  [MeasurableSpace (B.Levi F ⧸ Subgroup.center (B.Levi F))]
  [BorelSpace (B.Levi F ⧸ Subgroup.center (B.Levi F))]

/-- Every regular Haar measure on the full central quotient of a block Levi is
right invariant. -/
theorem haar_leviCentralQuotient_isMulRightInvariant
    (μ : Measure (B.Levi F ⧸ Subgroup.center (B.Levi F)))
    [μ.IsHaarMeasure] [μ.Regular] : Measure.IsMulRightInvariant μ := by
  constructor
  intro q
  have : (Measure.map (fun x => x * q) μ).Regular :=
    Measure.Regular.map (μ := μ) (Homeomorph.mulRight q)
  rw [Measure.isMulLeftInvariant_eq_smul_of_regular
    (Measure.map (fun x => x * q) μ) μ,
    ← Measure.modularCharacterFun_eq_haarScalarFactor]
  change Measure.modularCharacter q • μ = μ
  rw [leviCentralQuotient_positiveCharacter_eq_one, one_smul]

end GeneralLinear.BlockShape

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- Every Borel Haar measure on the full central quotient of an actual p-adic
standard block Levi is right invariant and invariant under inversion. -/
theorem leviCentralQuotientHaar_unimodular (T : F.TopologicalData) {n : ℕ}
    (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    ∀ [MeasurableSpace (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier))]
      [BorelSpace (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier))]
      (μ : Measure (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)))
      [μ.IsHaarMeasure],
      μ.IsMulRightInvariant ∧ μ.IsInvInvariant := by
  let := T.topology
  intro _ _ μ _
  let := T.leviTopologicalGroup B
  let Q := B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)
  have h := (glBlockCentralQuotientTopology p F T n).2 B
  let : T2Space Q := h.2.1
  let : LocallyCompactSpace Q := h.2.2.1
  let : SecondCountableTopology Q := h.2.2.2.1
  have hR : μ.IsMulRightInvariant := B.haar_leviCentralQuotient_isMulRightInvariant μ
  exact ⟨hR, isInvInvariant_of_isMulRightInvariant μ⟩

end PadicField.TopologicalData

end Langlands
