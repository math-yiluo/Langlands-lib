import Langlands.Global.Arithmetic.CMCharacterStatement
import Langlands.Global.IntegralFiniteAdeles
import Langlands.Representation.Twist.ContinuousCharacterProof
import Langlands.Topology.LocallyProfiniteProof
import Mathlib.Topology.Algebra.Group.Units

noncomputable section

universe u

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Filter Topology
open scoped WithZero

namespace Langlands.Global

namespace IntegralUnitCharacterExtension

variable {K : Type u} [Field K] [NumberField K] (w : FinitePlace K)

private abbrev inclusion :
    (w.adicCompletionIntegers K)ˣ →* (FiniteCompletion K w)ˣ :=
  Units.map (w.adicCompletionIntegers K).subtype.toMonoidHom

private theorem continuous_inclusion : Continuous (inclusion w) :=
  continuous_subtype_val.units_map _

private theorem compact_units : CompactSpace (w.adicCompletionIntegers K)ˣ := by
  let : CompactSpace (w.adicCompletionIntegers K) :=
    isCompact_iff_compactSpace.mp (isCompact_adicCompletionIntegers K w)
  infer_instance

private theorem nonarchimedean_units :
    NonarchimedeanGroup (w.adicCompletionIntegers K)ˣ := by
  let : ValuativeRel (FiniteCompletion K w) :=
    (CompletionPadic.topologicalData w).valuativeRel
  let : IsNonarchimedeanLocalField (FiniteCompletion K w) :=
    (CompletionPadic.topologicalData w).localField
  let : TotallyDisconnectedSpace (FiniteCompletion K w) := inferInstance
  let : CompactSpace (w.adicCompletionIntegers K)ˣ := compact_units w
  have hcont : Continuous (fun a : (w.adicCompletionIntegers K)ˣ =>
      ((a : w.adicCompletionIntegers K) : FiniteCompletion K w)) :=
    continuous_subtype_val.comp Units.continuous_val
  have hinj : Function.Injective (fun a : (w.adicCompletionIntegers K)ˣ =>
      ((a : w.adicCompletionIntegers K) : FiniteCompletion K w)) :=
    Subtype.val_injective.comp Units.val_injective
  let : TotallyDisconnectedSpace (w.adicCompletionIntegers K)ˣ :=
    ⟨isTotallyDisconnected_of_image
      hcont.continuousOn hinj (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
  refine { is_nonarchimedean := ?_ }
  intro U hU
  obtain ⟨H, _, hH⟩ :=
    ((Langlands.Topology.LocallyProfiniteProof.vanDantzig _).mp
      Langlands.Topology.isLocallyProfinite_of_mathlib).2 U hU
  exact ⟨H, hH⟩

private theorem finite_order (η : (w.adicCompletionIntegers K)ˣ →ₜ* ℂˣ) :
    ∃ n : ℕ, 0 < n ∧ η ^ n = 1 := by
  let := compact_units w
  let := nonarchimedean_units w
  have hopen : IsOpen (η.toMonoidHom.ker : Set (w.adicCompletionIntegers K)ˣ) :=
    Langlands.isOpen_ker_of_continuous_complex_character η.toMonoidHom η.continuous
  let := Subgroup.quotient_finite_of_isOpen η.toMonoidHom.ker hopen
  refine ⟨η.toMonoidHom.ker.index,
    Nat.pos_of_ne_zero η.toMonoidHom.ker.index_ne_zero_of_finite, ?_⟩
  apply ContinuousMonoidHom.ext
  intro a
  rw [ContinuousMonoidHom.pow_apply]
  exact (map_pow η a _).symm.trans
    (MonoidHom.mem_ker.mp (η.toMonoidHom.ker.pow_index_mem a))

private def valuationLog (a : (FiniteCompletion K w)ˣ) : ℤ :=
  WithZero.log (Valued.v (a : FiniteCompletion K w))

private theorem continuous_valuationLog : Continuous (valuationLog w) := by
  apply IsLocallyConstant.continuous
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro a
  have h := Units.continuous_val.continuousAt.preimage_mem_nhds
    (Valued.locally_const (Valued.v.ne_zero_iff.mpr a.ne_zero))
  filter_upwards [h] with b hb
  exact congrArg WithZero.log hb

private theorem valuationLog_mul (a b : (FiniteCompletion K w)ˣ) :
    valuationLog w (a * b) = valuationLog w a + valuationLog w b := by
  simp only [valuationLog, Units.val_mul, map_mul,
    WithZero.log_mul (Valued.v.ne_zero_iff.mpr a.ne_zero)
      (Valued.v.ne_zero_iff.mpr b.ne_zero)]

private def splittingUnit : (FiniteCompletion K w)ˣ :=
  Units.mk0 ((valuedAdicCompletion_surjective K w) (WithZero.exp (1 : ℤ))).choose
    (by
      intro h
      have hval := ((valuedAdicCompletion_surjective K w)
        (WithZero.exp (1 : ℤ))).choose_spec
      rw [h, map_zero] at hval
      exact WithZero.exp_ne_zero hval.symm)

private theorem splittingUnit_value :
    Valued.v (splittingUnit w : FiniteCompletion K w) = WithZero.exp (1 : ℤ) :=
  ((valuedAdicCompletion_surjective K w) (WithZero.exp (1 : ℤ))).choose_spec

private def unitPartField (a : (FiniteCompletion K w)ˣ) : (FiniteCompletion K w)ˣ :=
  a * splittingUnit w ^ (-valuationLog w a)

private theorem unitPartField_value (a : (FiniteCompletion K w)ˣ) :
    Valued.v (unitPartField w a : FiniteCompletion K w) = 1 := by
  rw [unitPartField, Units.val_mul, map_mul, Units.val_zpow_eq_zpow_val,
    map_zpow₀, splittingUnit_value, ← WithZero.exp_zsmul]
  simp only [smul_eq_mul, mul_one]
  change Valued.v (a : FiniteCompletion K w) *
    WithZero.exp (-WithZero.log (Valued.v (a : FiniteCompletion K w))) = 1
  calc
    _ = WithZero.exp (WithZero.log (Valued.v (a : FiniteCompletion K w))) *
        WithZero.exp (-WithZero.log (Valued.v (a : FiniteCompletion K w))) := by
      rw [WithZero.exp_log (Valued.v.ne_zero_iff.mpr a.ne_zero)]
    _ = 1 := by rw [← WithZero.exp_add]; simp

private def unitPart (a : (FiniteCompletion K w)ˣ) : (w.adicCompletionIntegers K)ˣ where
  val := ⟨(unitPartField w a : FiniteCompletion K w), (unitPartField_value w a).le⟩
  inv := ⟨((unitPartField w a)⁻¹ : (FiniteCompletion K w)ˣ),
    by
      change Valued.v (((unitPartField w a)⁻¹ : (FiniteCompletion K w)ˣ) :
        FiniteCompletion K w) ≤ 1
      rw [Units.val_inv_eq_inv_val, map_inv₀, unitPartField_value, inv_one]⟩
  val_inv := by apply Subtype.ext; exact Units.mul_inv (unitPartField w a)
  inv_val := by apply Subtype.ext; exact Units.inv_mul (unitPartField w a)

private theorem unitPart_mul (a b : (FiniteCompletion K w)ˣ) :
    unitPart w (a * b) = unitPart w a * unitPart w b := by
  apply Units.ext
  apply Subtype.ext
  change ((a * b) * splittingUnit w ^ (-valuationLog w (a * b)) :
      (FiniteCompletion K w)ˣ).val =
    ((a * splittingUnit w ^ (-valuationLog w a)) *
      (b * splittingUnit w ^ (-valuationLog w b))).val
  congr 1
  rw [valuationLog_mul, neg_add, zpow_add]
  ac_rfl

private theorem continuous_unitPart : Continuous (unitPart w) := by
  have hpow : Continuous (fun a : (FiniteCompletion K w)ˣ =>
      splittingUnit w ^ (-valuationLog w a)) :=
    (continuous_of_discreteTopology (f := fun n : ℤ => splittingUnit w ^ (-n))).comp
      (continuous_valuationLog w)
  have hfield : Continuous (unitPartField w) := continuous_id.mul hpow
  apply Units.continuous_iff.mpr
  exact ⟨(Units.continuous_val.comp hfield).subtype_mk _,
    (Units.continuous_val.comp hfield.inv).subtype_mk _⟩

private theorem unitPart_inclusion (a : (w.adicCompletionIntegers K)ˣ) :
    unitPart w (inclusion w a) = a := by
  have hv : Valued.v (((a : w.adicCompletionIntegers K) : FiniteCompletion K w)) = 1 :=
    adicCompletionIntegers.isUnit_iff_valued_eq_one.mp a.isUnit
  have hlog : valuationLog w (inclusion w a) = 0 := by
    change WithZero.log (Valued.v (((a : w.adicCompletionIntegers K) :
      FiniteCompletion K w))) = 0
    rw [hv, WithZero.log_one]
  apply Units.ext
  apply Subtype.ext
  change (inclusion w a * splittingUnit w ^ (-valuationLog w (inclusion w a))).val = _
  rw [hlog]
  simp [inclusion]

end IntegralUnitCharacterExtension

/-- Every continuous character of the actual integral units admits a
finite-order continuous extension to the local multiplicative group. -/
theorem integralUnitCharacterExtension : IntegralUnitCharacterExtensionStatement.{u} := by
  intro K _ _ w η
  let P : (FiniteCompletion K w)ˣ →ₜ* (w.adicCompletionIntegers K)ˣ :=
    { toFun := IntegralUnitCharacterExtension.unitPart w
      map_one' := by
        simpa using IntegralUnitCharacterExtension.unitPart_inclusion w 1
      map_mul' := IntegralUnitCharacterExtension.unitPart_mul w
      continuous_toFun := IntegralUnitCharacterExtension.continuous_unitPart w }
  refine ⟨η.comp P, ?_, ?_⟩
  · obtain ⟨n, hn, hη⟩ := IntegralUnitCharacterExtension.finite_order w η
    refine ⟨n, hn, ?_⟩
    apply ContinuousMonoidHom.ext
    intro a
    rw [ContinuousMonoidHom.pow_apply]
    change η (P a) ^ n = 1
    simpa only [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.coe_one, Pi.one_apply] using
      congrArg (fun f : (w.adicCompletionIntegers K)ˣ →ₜ* ℂˣ => f (P a)) hη
  · intro a
    change η (IntegralUnitCharacterExtension.unitPart w
      (IntegralUnitCharacterExtension.inclusion w a)) = η a
    rw [IntegralUnitCharacterExtension.unitPart_inclusion]

end Langlands.Global
