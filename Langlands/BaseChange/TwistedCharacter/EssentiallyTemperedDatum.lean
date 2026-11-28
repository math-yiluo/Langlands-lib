import Langlands.BaseChange.TwistedCharacter.StandardTraceFamily
import Langlands.BaseChange.PseudoCoefficient
import Langlands.Representation.Classification.RegularLanglandsDataUniquenessProof
import Langlands.Representation.Classification.UnitaryWeylRigidityProof
import Langlands.Representation.Twist.UnitaryModCenterProof
import Langlands.Representation.Induction.SingleBlock
import Langlands.Group.GL.OneBlockShape

/-! # Langlands data of essentially tempered irreducible representations -/

noncomputable section

namespace Langlands.BaseChange

open CategoryTheory GeneralLinear HarmonicAnalysis MeasureTheory PadicField.TopologicalData

universe v w

section Padic

variable {p : ℕ} [Fact p.Prime] {E : PadicField.{v} p} (T : E.TopologicalData)

/-- Every positive real number is the parameter of a real determinant power. -/
theorem exists_realPowerParameter_eq (r : ℝ) (hr : 0 < r) :
    ∃ s : ℝ, (realPowerParameter T s : ℂ) = r := by
  obtain ⟨ha, ha1⟩ := UnitaryWeylRigidity.normalizedAbs_uniformizer_pos_ne_one T
  refine ⟨Real.logb (T.normalizedAbs T.uniformizer) r, ?_⟩
  show ((realPowerCharacter T.normalizedAbsUnits _ T.uniformizerUnit : ℂˣ) : ℂ) = _
  rw [coe_realPowerCharacter, normalizedAbsUnits_coe, uniformizerUnit_val,
    Real.rpow_logb ha ha1 hr]

theorem determinantUnramified_one (m : ℕ) :
    letI := T.valuativeRel
    letI := T.topology
    letI := T.localField
    determinantUnramified E.Carrier m 1 = 1 := by
  let := T.valuativeRel
  let := T.topology
  let := T.localField
  apply MonoidHom.ext
  intro g
  rw [determinantUnramified_apply, one_zpow]
  rfl

set_option maxHeartbeats 800000 in
/-- An irreducible representation that becomes tempered after an unramified twist is a
Langlands quotient of a tempered datum with a single block. -/
theorem exists_singleBlockDatum_of_twist_tempered {n : ℕ} (hn : 0 < n)
    (π : letI := T.topology; SmoothRep.{0,v,max v w} ℂ (GeneralLinear n E.Carrier))
    (hπ : letI := T.topology; π.representation.IsIrreducible)
    (ψ : GeneralLinear n E.Carrier →* ℂˣ)
    (hψ : letI := T.topology; IsUnramifiedCharacter ψ)
    (htemp : letI := T.topology; T.IsTempered (twist ψ π.representation)) :
    ∃ t : T.TemperedLanglandsDatum.{max v w} n,
      t.shape.length = 1 ∧ t.IsLanglandsQuotient π := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup n
  let := LocalFieldTopology.generalLinear_t2Space E.Carrier n
  let := LocalFieldTopology.generalLinear_locallyCompactSpace E.Carrier n
  let := LocalFieldTopology.generalLinear_totallyDisconnectedSpace E.Carrier n
  let i0 : Fin n := ⟨0, hn⟩
  have hψeq : ψ = determinantUnramified E.Carrier n (ψ (Iwasawa.diagonalUnits
      (Pi.mulSingle i0 (LocalFieldData.ofInstances E.Carrier).uniformizerUnit))) :=
    eq_detOrderCharacter_of_isUnramified E.Carrier i0 ψ hψ
  set z := ψ (Iwasawa.diagonalUnits
      (Pi.mulSingle i0 (LocalFieldData.ofInstances E.Carrier).uniformizerUnit)) with hz
  have hw0 : 0 < ‖((z⁻¹ : ℂˣ) : ℂ)‖ := norm_pos_iff.mpr (Units.ne_zero _)
  obtain ⟨s, hs⟩ := exists_realPowerParameter_eq T ‖((z⁻¹ : ℂˣ) : ℂ)‖ hw0
  let u : ℂˣ := z⁻¹ * (realPowerParameter T s)⁻¹
  have hu : ‖(u : ℂ)‖ = 1 := by
    change ‖((z⁻¹ : ℂˣ) : ℂ) * (((realPowerParameter T s)⁻¹ : ℂˣ) : ℂ)‖ = 1
    rw [norm_mul, Units.val_inv_eq_inv_val (realPowerParameter T s), norm_inv, hs,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw0, mul_inv_cancel₀ hw0.ne']
  let χu := determinantUnramified E.Carrier n u
  have hχu : IsOpen (χu.ker : Set (GeneralLinear n E.Carrier)) :=
    isOpen_ker_determinantUnramified E.Carrier n u
  let ρ := twist χu (twist ψ π.representation)
  have hρs : IsSmooth ρ :=
    (isSmooth_twist_iff χu _ hχu).mpr ((isSmooth_twist_iff ψ _ hψ.isOpen_ker).mpr π.isSmooth)
  let δ : SmoothRep.{0,v,max v w} ℂ (GeneralLinear n E.Carrier) := SmoothRep.of ρ hρs
  have hδtemp : T.IsTempered δ.representation := by
    let := T.centralQuotientMeasurableSpace n
    have := T.centralQuotientBorelSpace n
    intro μ _
    exact isTemperedModCenter_unitaryTwist χu hχu
      (norm_determinantUnramified E.Carrier n u hu) μ (htemp μ)
  have hδirr : δ.representation.IsIrreducible :=
    (isIrreducible_twist_iff _ _).mpr ((isIrreducible_twist_iff _ _).mpr hπ)
  let t : T.TemperedLanglandsDatum.{max v w} n :=
    { shape := CuspidalSupport.LeviAdmissibility.oneBlock n hn
      blocks := fun _ => δ
      irreducible := fun _ => hδirr
      tempered := fun _ => hδtemp
      exponent := fun _ => s
      strictAnti := by
        change StrictAnti (fun _ : Fin 1 => s)
        intro i j hij
        have heq : i = j := Subsingleton.elim _ _
        subst j
        exact (lt_irrefl _ hij).elim }
  refine ⟨t, rfl, ?_⟩
  let τ := fun i => (T.twistedBlocks t.shape t.blocks t.exponent i).representation
  let i1 : Fin t.shape.length := ⟨0, Nat.one_pos⟩
  let e1 := T.singleBlockNormalizedProductEquiv t.shape rfl τ
    (fun i => (T.twistedBlocks t.shape t.blocks t.exponent i).isSmooth) i1
  have hr : ((GeneralLinear.reindex (R := E.Carrier)
      (finCongr (t.shape.singleBlock_size rfl i1))).symm.toMonoidHom :
        GeneralLinear n E.Carrier →* GeneralLinear n E.Carrier) = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro g
    apply Units.ext
    ext a b
    rfl
  have hchar : T.determinantPowerCharacter n s * (χu * ψ) = 1 := by
    rw [determinantPowerCharacter_eq_determinantUnramified T n s, hψeq,
      ← determinantUnramified_mul, ← determinantUnramified_mul]
    have h1 : realPowerParameter T s * (u * z) = 1 := by
      change realPowerParameter T s * (z⁻¹ * (realPowerParameter T s)⁻¹ * z) = 1
      rw [mul_comm z⁻¹, mul_assoc, inv_mul_cancel, mul_one, mul_inv_cancel]
    rw [h1]
    exact determinantUnramified_one T n
  have hτ : (τ i1).comp (GeneralLinear.reindex (R := E.Carrier)
      (finCongr (t.shape.singleBlock_size rfl i1))).symm.toMonoidHom = π.representation := by
    rw [hr]
    change MonoidHom.comp (twist (T.determinantPowerCharacter n s)
      (twist χu (twist ψ π.representation))) (MonoidHom.id _) = π.representation
    rw [MonoidHom.comp_id, twist_twist χu ψ, twist_twist, hchar, twist_one]
  let e : t.standardModule.representation.Equiv π.representation :=
    e1.trans (equivOfRepresentationEq hτ)
  exact ⟨hπ, e.toIntertwiningMap, e.surjective⟩

set_option maxHeartbeats 800000 in
/-- A tempered datum whose Langlands quotient becomes tempered after an unramified twist has
a single block. -/
theorem shape_length_eq_one_of_twist_tempered {n : ℕ} (hn : 0 < n)
    (t : T.TemperedLanglandsDatum.{max v w} n)
    (π : letI := T.topology; SmoothRep.{0,v,max v w} ℂ (GeneralLinear n E.Carrier))
    (hq : t.IsLanglandsQuotient π)
    (ψ : GeneralLinear n E.Carrier →* ℂˣ)
    (hψ : letI := T.topology; IsUnramifiedCharacter ψ)
    (htemp : letI := T.topology; T.IsTempered (twist ψ π.representation)) :
    t.shape.length = 1 := by
  let := T.topology
  obtain ⟨t', h1, hq'⟩ := exists_singleBlockDatum_of_twist_tempered.{v,w} T hn π hq.1 ψ hψ htemp
  obtain ⟨a, -, -⟩ := glRegularLanglandsDataUniqueness.{v,w} p E T n hn t t' π π hq hq'
    ⟨Iso.refl π⟩
  have hc := Fintype.card_congr a.toEquiv
  simpa [h1] using hc

end Padic

end Langlands.BaseChange
