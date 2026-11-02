import Langlands.Representation.Classification.SegmentSquareIntegrabilityStatement
import Langlands.Representation.Classification.SegmentSpecialJacquetExponentProof
import Langlands.LocalField.SmoothCharacterNormProof
import Langlands.Representation.Classification.TwistedProductCharacterTwistProof
import Langlands.Representation.Classification.ConstituentCompatibilityAlgebraicProof
import Langlands.Representation.CuspidalSupport.CuspidalEmbeddingProof
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.Representation.Exponents.Chambers
import Langlands.Representation.Classification.TemperedExponentEdgeProof
import Langlands.Representation.Classification.SquareIntegrableExponentProof
import Mathlib.Tactic

/-!
# Essential square-integrability of every weak segment special quotient

The published Jacquet norm formula, scalar norm decomposition and analytic
criterion combine with actual twisting and finite positive-cone arithmetic.
-/

noncomputable section

namespace Langlands.Classification

open Finset

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The weak segment quotient relation survives an actual real determinant
twist. No uniqueness of the quotient is needed. -/
private theorem segmentQuotient_realPowerTwist
    (Δ : T.Segment.{max uF uV, uF})
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hπ : T.IsSegmentQuotient Δ π) (s : ℝ) :
    letI := T.topology
    T.IsSegmentQuotient (Δ.twist s)
      (π.twist (T.determinantPowerCharacter Δ.degree s)
        (T.isOpen_ker_determinantPowerCharacter Δ.degree s)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  obtain ⟨A, hA, hq⟩ := hπ
  let As := GeneralLinear.SupercuspidalRep.twist
    (T.determinantPowerCharacter Δ.rank s)
    (T.isOpen_ker_determinantPowerCharacter Δ.rank s)
    (T.ker_determinant_le_ker_determinantPowerCharacter Δ.rank s) A
  refine ⟨As, ?_, ?_⟩
  · exact congrArg (T.supercuspidalClassRealPowerTwist Δ.rank s) hA
  · let χ : Induction.SmoothCharacter ℂ F.Carrierˣ :=
      ⟨realPowerCharacter T.normalizedAbsUnits s,
        isOpen_ker_realPowerCharacter _ T.isOpen_ker_normalizedAbsUnits s⟩
    obtain ⟨e⟩ := twistedProductCharacterTwist.{uF, max uF uV} F T
      Δ.degree Δ.degree_pos (GeneralLinear.BlockShape.uniform Δ.length Δ.rank Δ.rank_pos)
      χ (fun _ => A.obj) (fun i => ((i : ℕ) : ℝ))
    have hq' := (isIrreducibleQuotient_twist_iff
      (T.determinantPowerCharacter Δ.degree s)
      (T.segmentInduced A.obj Δ.length Δ.rank_pos).representation π.representation).mpr hq
    exact hq'.of_equiv e

private theorem segmentQuotient_isAdmissible
    (Δ : T.Segment.{max uF uV, uF})
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hπ : T.IsSegmentQuotient Δ π) :
    letI := T.topology
    IsAdmissible π.representation := by
  let := T.topology
  obtain ⟨_, _, hq⟩ := hπ
  exact (CuspidalSupport.cuspidalEmbedding F T Δ.degree π hq.1).1

/-- Restrict the actual locally constant Schur character to scalar matrices. -/
private theorem exists_smooth_scalarCharacter {n : ℕ}
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (ha : letI := T.topology; IsAdmissible π.representation)
    (hi : letI := T.topology; Representation.IsIrreducible π.representation) :
    letI := T.topology
    ∃ ω : F.Carrierˣ →* ℂˣ, IsOpen (ω.ker : Set F.Carrierˣ) ∧
      HasScalarCharacter π.representation GeneralLinear.scalar ω := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  obtain ⟨η, ⟨hη, hact⟩, _⟩ := admissibleSchur_centralCharacter π.representation ha hi
  let ω := η.comp (GeneralLinear.scalarToCenter (n := n))
  have hcont : Continuous
      (GeneralLinear.scalarToCenter : F.Carrierˣ →
        Subgroup.center (GeneralLinear n F.Carrier)) :=
    (T.generalLinearScalar n).continuous.subtype_mk _
  refine ⟨ω, ?_, ?_⟩
  · exact (hη.comp_continuous hcont).isOpen_fiber 1
  · intro a v
    exact hact (GeneralLinear.scalarToCenter a) v

private theorem scalarCharacter_realPowerTwist {n : ℕ}
    {V : Type (max uF uV)} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (ω : F.Carrierˣ →* ℂˣ)
    (hω : HasScalarCharacter ρ GeneralLinear.scalar ω) (s : ℝ) :
    HasScalarCharacter (realPowerTwist (T.determinantNorm n) s ρ)
      GeneralLinear.scalar (ω * (realPowerCharacter T.normalizedAbsUnits s) ^ n) :=
  (glConstituentCentralCharacterFor F.Carrier n V V ρ ρ ω
    (realPowerCharacter T.normalizedAbsUnits s)).2.2 hω

private theorem scalarNorm_realPowerTwist
    (ω : F.Carrierˣ →* ℂˣ) (c : ℝ)
    (hc : ∀ a : F.Carrierˣ, ‖(ω a : ℂ)‖ = T.normalizedAbs (a : F.Carrier) ^ c)
    (n : ℕ) (s : ℝ) (a : F.Carrierˣ) :
    ‖((ω * (realPowerCharacter T.normalizedAbsUnits s) ^ n) a : ℂ)‖ =
      T.normalizedAbs (a : F.Carrier) ^ (c + (n : ℝ) * s) := by
  have ha := T.normalizedAbs_pos a.ne_zero
  simp only [MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, Units.val_pow_eq_pow_val,
    norm_mul, norm_pow, coe_realPowerCharacter, T.normalizedAbsUnits_coe]
  rw [hc, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg ha.le _), ← Real.rpow_mul_natCast ha.le,
    ← Real.rpow_add ha]
  congr 1
  ring

private theorem centeredSegmentExponent (r m k : ℕ) (hr : 0 < r) (c P : ℝ) :
    (c + (r : ℝ) * (-c / (r : ℝ) - ((m : ℝ) - 1) / 2)) * (k : ℝ) +
        (r : ℝ) * (k : ℝ) * ((2 * (m : ℝ) - (k : ℝ) - 1) / 2 - P) =
      (r : ℝ) * (k : ℝ) * (((m : ℝ) - (k : ℝ)) / 2 - P) := by
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp
  ring

private theorem initialSum_succ {l : ℕ} (w : Fin l → ℝ) {j : ℕ} (hj : j < l) :
    Exponents.partialSum w (j + 1) =
      Exponents.partialSum w j + w ⟨j, hj⟩ := by
  have hfilter :
      univ.filter (fun i : Fin l => (i : ℕ) < j + 1) =
        insert ⟨j, hj⟩ (univ.filter (fun i : Fin l => (i : ℕ) < j)) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · intro hi
      by_cases h : (i : ℕ) = j
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (by omega)
    · rintro (rfl | hi)
      · exact Nat.lt_succ_self j
      · omega
  unfold Exponents.partialSum
  rw [hfilter, sum_insert (by simp)]
  ring

private theorem initialSum_full {l : ℕ} (w : Fin l → ℝ) :
    Exponents.partialSum w l = ∑ i, w i := by
  unfold Exponents.partialSum
  simp

private theorem initialSum_centered {l : ℕ} (r : ℝ) (w : Fin l → ℝ)
    (j : ℕ) (hj : j ≤ l) :
    Exponents.partialSum
      (fun i => r * w i * (((∑ t, w t) - w i) / 2 - Exponents.partialSum w i)) j =
      r * Exponents.partialSum w j * ((∑ t, w t) - Exponents.partialSum w j) / 2 := by
  induction j with
  | zero => simp [Exponents.partialSum]
  | succ j ih =>
    rw [initialSum_succ _ (by omega), ih (by omega), initialSum_succ _ (by omega)]
    ring

/-- Positive consecutive interval lengths give the strict Casselman cone after
centering. This is a finite real arithmetic lemma; it assumes no representation
or analytic criterion. -/
private theorem centeredInterval_positiveRootCone {l : ℕ} (r : ℝ) (hr : 0 < r)
    (w : Fin l → ℝ) (hw : ∀ i, 0 < w i) :
    Exponents.IsPositiveRootCone
      (fun i => r * w i * (((∑ t, w t) - w i) / 2 - Exponents.partialSum w i)) := by
  constructor
  · rw [← initialSum_full, initialSum_centered _ _ _ le_rfl, initialSum_full]
    ring
  · intro j hj hjl
    rw [initialSum_centered _ _ _ hjl.le]
    have hp : 0 < Exponents.partialSum w j := by
      unfold Exponents.partialSum
      apply Finset.sum_pos'
      · intro i _
        exact (hw i).le
      · exact ⟨⟨0, by omega⟩, by simp [hj], hw _⟩
    have hq : 0 < (∑ i, w i) - Exponents.partialSum w j := by
      have hsplit := Finset.sum_filter_add_sum_filter_not univ
        (fun i : Fin l => (i : ℕ) < j) w
      have htail : 0 < ∑ i ∈ univ.filter (fun i : Fin l => ¬ (i : ℕ) < j), w i := by
        apply Finset.sum_pos'
        · intro i _
          exact (hw i).le
        · exact ⟨⟨j, hjl⟩, by simp, hw _⟩
      unfold Exponents.partialSum
      linarith
    exact div_pos (mul_pos (mul_pos hr hp) hq) (by norm_num)

/-- Convert the Jacquet norm identity for a normalized segment to a real part
in the strict positive root cone. -/
private theorem centeredNormFormula_positiveRootCone
    {l : ℕ} (r m : ℕ) (hr : 0 < r)
    (k : Fin l → ℕ) (hk : ∀ i, 0 < k i) (hm : ∑ i, k i = m)
    (ω : F.Carrierˣ →* ℂˣ) (c : ℝ)
    (hω : ∀ a : F.Carrierˣ, ‖(ω a : ℂ)‖ =
      T.normalizedAbs (a : F.Carrier) ^
        (c + (r : ℝ) * (-c / (r : ℝ) - ((m : ℝ) - 1) / 2)))
    (χ : (Fin l → F.Carrierˣ) →* ℂˣ)
    (hχ : ∀ a : Fin l → F.Carrierˣ,
      ‖(χ a : ℂ)‖ = ∏ i,
        ‖(ω (a i) : ℂ)‖ ^ k i *
          T.normalizedAbs (a i : F.Carrier) ^
            ((r : ℝ) * (k i : ℝ) *
              ((2 * (m : ℝ) - (k i : ℝ) - 1) / 2 -
                ((∑ j ∈ univ.filter (fun j : Fin l => j < i), k j : ℕ) : ℝ)))) :
    ∃ x : Fin l → ℝ, T.IsRealPartOf χ x ∧ Exponents.IsPositiveRootCone x := by
  let w : Fin l → ℝ := fun i => (k i : ℝ)
  let x : Fin l → ℝ := fun i =>
    (r : ℝ) * w i * (((∑ j, w j) - w i) / 2 - Exponents.partialSum w i)
  have hm' : ∑ i, w i = (m : ℝ) := by
    change ∑ i, (k i : ℝ) = (m : ℝ)
    exact_mod_cast hm
  refine ⟨x, ?_, centeredInterval_positiveRootCone (r : ℝ)
    (by exact_mod_cast hr) w (fun i => by
      change (0 : ℝ) < (k i : ℝ)
      exact_mod_cast hk i)⟩
  intro a
  rw [hχ]
  apply Finset.prod_congr rfl
  intro i _
  have ha := T.normalizedAbs_pos (a i).ne_zero
  rw [hω, ← Real.rpow_mul_natCast ha.le, ← Real.rpow_add ha]
  have hprefix :
      ((∑ j ∈ univ.filter (fun j : Fin l => j < i), k j : ℕ) : ℝ) =
        Exponents.partialSum w i := by
    simp [Exponents.partialSum, w]
  rw [hprefix, centeredSegmentExponent r m (k i) hr c]
  congr 1
  simp only [x, w, hm']

/-- Apply the published analytic criterion to positive-cone Jacquet real parts.
The elementary edge theorem supplies scalar unitarity from the weak bounds. -/
private theorem squareIntegrable_of_jacquetPositiveRootCone
    {n : ℕ} (hn : 0 < n)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (ha : letI := T.topology; IsAdmissible π.representation)
    (hi : letI := T.topology; Representation.IsIrreducible π.representation)
    (hparts : letI := T.topology; ∀ (B : GeneralLinear.BlockShape n)
      (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ),
      T.IsJacquetExponent B π.representation χ →
        ∃ x : Fin B.length → ℝ,
          T.IsRealPartOf χ x ∧ Exponents.IsPositiveRootCone x) :
    letI := T.topology
    T.IsSquareIntegrable π.representation := by
  let := T.topology
  let := hi
  let : Nontrivial π :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
      π.representation.asModule
  obtain ⟨ω, _, hact⟩ := exists_smooth_scalarCharacter F T π ha hi
  have hweak : ∀ (B : GeneralLinear.BlockShape n)
      (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ),
      T.IsJacquetExponent B π.representation χ →
      ∀ a : Fin B.length → F.Carrierˣ,
        Monotone (fun i => T.normalizedAbs (a i : F.Carrier)) →
          ‖(χ a : ℂ)‖ ≤ 1 := by
    intro B χ hχ
    obtain ⟨x, hx, hcone⟩ := hparts B χ hχ
    exact (hx.isClosedPositiveRootCone_iff.mp hcone.isClosedPositiveRootCone).2
  have hunitary := (glTemperedExponentEdge.{uF, max uF uV}).2 p F T n hn π
    π.representation ω π.isSmooth hact hweak
  apply (glSquareIntegrableExponentCriterion.{uF, max uF uV}
    p F T n hn π π.representation ω ha hact).mpr
  refine ⟨hunitary.2.1, ?_⟩
  intro B χ hχ
  obtain ⟨x, hx, hcone⟩ := hparts B χ hχ
  exact (hx.isPositiveRootCone_iff.mp hcone).2

/-- Every weak segment special quotient is analytically essentially
square-integrable after an actual real determinant twist. -/
theorem segmentSpecialEssentialSquareIntegrability :
    SegmentSpecialEssentialSquareIntegrability.{uF, uV} F T := by
  let := T.topology
  intro Δ π hπ
  have hπkeep := hπ
  obtain ⟨A, hA, _⟩ := hπkeep
  obtain ⟨ω, hopen, hact⟩ :=
    exists_smooth_scalarCharacter F T A.obj A.property.2.1 A.property.1
  obtain ⟨c, hc⟩ :=
    (PadicField.TopologicalData.smoothCharacterNormDecomposition F T ω hopen).exists
  let s : ℝ := -c / (Δ.rank : ℝ) - ((Δ.length : ℝ) - 1) / 2
  let As := GeneralLinear.SupercuspidalRep.twist
    (T.determinantPowerCharacter Δ.rank s)
    (T.isOpen_ker_determinantPowerCharacter Δ.rank s)
    (T.ker_determinant_le_ker_determinantPowerCharacter Δ.rank s) A
  let πs := π.twist (T.determinantPowerCharacter Δ.degree s)
    (T.isOpen_ker_determinantPowerCharacter Δ.degree s)
  let ωs := ω * (realPowerCharacter T.normalizedAbsUnits s) ^ Δ.rank
  have hAs : (Δ.twist s).base.IsRepresentedBy As :=
    congrArg (T.supercuspidalClassRealPowerTwist Δ.rank s) hA
  have hωs : HasScalarCharacter As.obj.representation GeneralLinear.scalar ωs :=
    scalarCharacter_realPowerTwist F T A.obj.representation ω hact s
  have hπs : T.IsSegmentQuotient (Δ.twist s) πs :=
    segmentQuotient_realPowerTwist F T Δ π hπ s
  have hnorm : ∀ a : F.Carrierˣ, ‖(ωs a : ℂ)‖ =
      T.normalizedAbs (a : F.Carrier) ^
        (c + (Δ.rank : ℝ) *
          (-c / (Δ.rank : ℝ) - ((Δ.length : ℝ) - 1) / 2)) :=
    scalarNorm_realPowerTwist F T ω c hc Δ.rank s
  have hparts : ∀ (B : GeneralLinear.BlockShape Δ.degree)
      (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ),
      T.IsJacquetExponent B πs.representation χ →
        ∃ x : Fin B.length → ℝ,
          T.IsRealPartOf χ x ∧ Exponents.IsPositiveRootCone x := by
    intro B χ hχ
    obtain ⟨k, hk, _, hm, hχnorm⟩ :=
      segmentSpecialJacquetExponentNormFormula.{uF, uV} F T
        (Δ.twist s) As ωs hAs hωs πs hπs B χ hχ
    exact centeredNormFormula_positiveRootCone F T Δ.rank Δ.length Δ.rank_pos
      k hk hm ωs c hnorm χ hχnorm
  have ha := segmentQuotient_isAdmissible F T (Δ.twist s) πs hπs
  obtain ⟨_, _, hq⟩ := hπs
  have hsi := squareIntegrable_of_jacquetPositiveRootCone F T
    Δ.degree_pos πs ha hq.1 hparts
  refine ⟨-s, ?_⟩
  rw [neg_neg]
  change T.IsSquareIntegrable πs.representation
  exact hsi

end Langlands.Classification
