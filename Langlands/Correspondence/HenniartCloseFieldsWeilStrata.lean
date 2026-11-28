import Langlands.Correspondence.HenniartLocalWeilSwanBreak
import Langlands.Correspondence.HenniartWeilSwanBreak
import Langlands.LocalFactor.Ramification.CloseFieldsWeilQuotientProof
import Langlands.Weil.Representation.FilteredQuotientClassTransport

/-! # Refined Weil orbit strata of close fields -/

noncomputable section

set_option autoImplicit false

universe u v

namespace Langlands.Henniart

open Correspondence FiniteRepresentation
open Weil.Local (localWeilGroup localDegree localResidueField)

attribute [local instance] LocalField.Laurent.valuativeRel

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

local notation "X" => LaurentSeries (localResidueField F)
local notation "Ω" => SeparableClosure X
local notation "W" => localWeilGroup F
local notation "W'" => Weil.Local.SepClosed.localWeilGroup X Ω
local notation "I" => VirtualRepresentation.LocalWeil.Ramification.upperGroup F
local notation "I'" => VirtualRepresentation.LocalWeil.SepClosed.Ramification.upperGroup X Ω
local notation "e" => (F.canonicalTopologicalData.ramificationIndex : ℝ)
local notation "d" => localDegree F
local notation "d'" => Weil.Local.SepClosed.localDegree X Ω

private local instance upperNormal : (I e).Normal :=
  Subgroup.Normal.comap (Ramification.Padic.absoluteUpperRamificationGroup_normal F e)
    (Weil.Local.localProjection F).toMonoidHom

private local instance upperNormal' : (I' e).Normal :=
  Subgroup.Normal.comap (Ramification.Local.localAbsoluteUpperRamificationGroup_normal X Ω e)
    (Weil.Local.SepClosed.localProjection X Ω).toMonoidHom

local notation "π" => QuotientGroup.mk' (I e)
local notation "π'" => QuotientGroup.mk' (I' e)

private theorem padic_classLastBreak_eq (c : IsomorphismClasses.{0, u, v} ℂ W) :
    VirtualRepresentation.LocalWeil.Ramification.classLastBreak F c = sInf (trivialityParameters I c) :=
  Quotient.inductionOn c (fun _ => rfl)

private theorem laurent_classLastBreak_eq (c : IsomorphismClasses.{0, u, v} ℂ W') :
    VirtualRepresentation.LocalWeil.SepClosed.Ramification.classLastBreak X Ω c =
      sInf (trivialityParameters I' c) :=
  Quotient.inductionOn c (fun _ => rfl)

private theorem padic_swan_iff {k s : ℕ} (c : IrreducibleWeilClass.{u, v} F k.succPNat) :
    Numerical.HasWeilSwan F c s ↔
      (s : ℝ) = ((k + 1 : ℕ) : ℝ) *
        VirtualRepresentation.LocalWeil.Ramification.classLastBreak F (weilClassForget F c) := by
  obtain ⟨A, hA⟩ := Quotient.exists_rep (weilClassForget F c)
  change classOf A = weilClassForget F c at hA
  rw [← hA, VirtualRepresentation.LocalWeil.Ramification.classLastBreak_classOf]
  exact Numerical.hasWeilSwan_iff_eq_rank_mul_lastBreak F hA

private theorem padic_trivialOn_of_swan {k s : ℕ} (c : IrreducibleWeilClass.{u, v} F k.succPNat)
    (hc : Numerical.HasWeilSwan F c s) (hs : s < (k + 1) * F.canonicalTopologicalData.ramificationIndex) :
    (weilClassForget F c).IsTrivialOn (I e) := by
  obtain ⟨A, hA⟩ := Quotient.exists_rep (weilClassForget F c)
  change classOf A = weilClassForget F c at hA
  have hs' : (s : ℝ) < ((k + 1 : ℕ) : ℝ) * e := by exact_mod_cast hs
  have hb : 0 < e := by exact_mod_cast F.canonicalTopologicalData.ramificationIndex_pos
  have hpos : 0 < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
  have heq := (Numerical.hasWeilSwan_iff_eq_rank_mul_lastBreak F hA).mp hc
  have hlt := (mul_lt_mul_iff_of_pos_left hpos).mp (heq ▸ hs')
  have hAcont := (Numerical.weilRepresentative_continuous_irreducible F hA).1
  have htriv := (Ramification.HerbrandBridge.lastBreak_lt_iff_isTrivialAt F A hAcont hb).mp hlt
  rw [← hA, classOf_isTrivialOn]
  exact htriv

private theorem laurent_trivialOn_of_swan {k s : ℕ}
    (c : LocalNumerical.IrreducibleWeilClass.{u, u, v} X Ω k.succPNat)
    (hc : LocalNumerical.HasWeilSwan X Ω c s)
    (hs : s < (k + 1) * F.canonicalTopologicalData.ramificationIndex) :
    (LocalNumerical.weilClassForget X Ω c).IsTrivialOn (I' e) := by
  obtain ⟨A, hA⟩ := Quotient.exists_rep (LocalNumerical.weilClassForget X Ω c)
  change classOf A = LocalNumerical.weilClassForget X Ω c at hA
  have hs' : (s : ℝ) < ((k + 1 : ℕ) : ℝ) * e := by exact_mod_cast hs
  have hb : 0 < e := by exact_mod_cast F.canonicalTopologicalData.ramificationIndex_pos
  have htriv := (LocalNumerical.isTrivialAt_iff_of_hasWeilSwan X Ω hA hc hb).mpr hs'
  rw [← hA, classOf_isTrivialOn]
  exact htriv

set_option maxHeartbeats 1400000 in
private theorem swan_transport_iff {k s : ℕ}
    (φ : (W ⧸ I e) ≃ₜ* (W' ⧸ I' e))
    (hφ : ∀ r : ℝ, 0 ≤ r → r ≤ e →
      ((I r).map π).map φ.toMulEquiv.toMonoidHom = (I' r).map π')
    (c : ContinuousIrreducibleClasses.TrivialOn.{u, v} (I e) (k + 1)) :
    LocalNumerical.HasWeilSwan X Ω (continuousIrreducibleQuotientTransport φ (k + 1) c).val s ↔
      Numerical.HasWeilSwan F c.val s := by
  let E := continuousIrreducibleQuotientTransport φ (k + 1)
  let c₁ := weilClassForget F (n := k.succPNat) c.val
  let c₂ := LocalNumerical.weilClassForget X Ω (n := k.succPNat) (E c).val
  have hset : trivialityParameters I' c₂ = trivialityParameters I c₁ := by
    ext r
    refine and_congr_right fun hr => ?_
    by_cases hre : r ≤ e
    · exact continuousIrreducibleQuotientTransport_isTrivialOn_iff φ c (I r) (I' r) (hφ r hr hre)
    · exact iff_of_true
        (IsomorphismClasses.isTrivialOn_of_le c₂ (VirtualRepresentation.LocalWeil.SepClosed.Ramification.upperGroup_antitone
          X Ω (le_of_not_ge hre)) (E c).property)
        (IsomorphismClasses.isTrivialOn_of_le c₁
          (VirtualRepresentation.LocalWeil.Ramification.upperGroup_antitone F (le_of_not_ge hre))
          c.property)
  refine (LocalNumerical.hasWeilSwan_iff_eq_weilSwanConductor X Ω (k := k) (s := s) (E c).val).trans
    (Iff.trans ?_ (padic_swan_iff F (k := k) (s := s) c.val).symm)
  change (s : ℝ) = ((k + 1 : ℕ) : ℝ) *
      VirtualRepresentation.LocalWeil.SepClosed.Ramification.classLastBreak X Ω c₂ ↔
    (s : ℝ) = ((k + 1 : ℕ) : ℝ) * VirtualRepresentation.LocalWeil.Ramification.classLastBreak F c₁
  rw [padic_classLastBreak_eq, laurent_classLastBreak_eq, hset]

set_option maxHeartbeats 1400000 in
private def laurentQuotientDegree
    (φ : (W ⧸ I e) ≃ₜ* (W' ⧸ I' e))
    (hdeg : ∀ w w', φ (π w) = π' w' → d w = d' w') :
    (W' ⧸ I' e) →ₜ* Weil.Degree := by
  have hker : I' e ≤ (d').toMonoidHom.ker := by
    intro w' hw'
    have hw : π' w' = 1 := (QuotientGroup.eq_one_iff w').mpr hw'
    have heq : φ (π 1) = π' w' := by rw [hw, map_one, map_one]
    have he := hdeg 1 w' heq
    rw [map_one] at he
    exact he.symm
  refine ⟨QuotientGroup.lift _ (d').toMonoidHom hker, ?_⟩
  exact (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr (d').continuous

set_option maxHeartbeats 1400000 in
private theorem unramified_transport {k : ℕ}
    (φ : (W ⧸ I e) ≃ₜ* (W' ⧸ I' e))
    (hdeg : ∀ w w', φ (π w) = π' w' → d w = d' w')
    (c : ContinuousIrreducibleClasses.TrivialOn.{u, v} (I e) (k + 1)) (z : ℂˣ) :
    let E := continuousIrreducibleQuotientTransport φ (k + 1)
    ∃ c' : ContinuousIrreducibleClasses.TrivialOn.{u, v} (I e) (k + 1),
      c'.val = Numerical.weilUnramifiedTwist F k z c.val ∧
      (E c').val = LocalNumerical.weilUnramifiedTwist X Ω k z (E c).val := by
  let χ := (Weil.Local.degreePowers z).comp (laurentQuotientDegree F φ hdeg)
  let χ₁ := χ.comp (φ : (W ⧸ I e) →ₜ* (W' ⧸ I' e))
  have hχ₁ : χ₁.comp ⟨π, QuotientGroup.continuous_mk⟩ = Weil.Local.localUnramifiedCharacter F z := by
    apply ContinuousMonoidHom.ext
    intro w
    obtain ⟨w', hw'⟩ := QuotientGroup.mk'_surjective (I' e) (φ (π w))
    change Weil.Local.degreePowers z (laurentQuotientDegree F φ hdeg (φ (π w))) =
      Weil.Local.degreePowers z (d w)
    rw [← hw']
    exact congrArg (Weil.Local.degreePowers z) (hdeg w w' hw'.symm).symm
  refine ⟨ContinuousIrreducibleClasses.TrivialOn.twistEquiv χ₁ (k + 1) c, ?_, ?_⟩
  · rw [ContinuousIrreducibleClasses.TrivialOn.twistEquiv_val, hχ₁]
    rfl
  · rw [continuousIrreducibleQuotientTransport_twist, ContinuousIrreducibleClasses.TrivialOn.twistEquiv_val]
    rfl

set_option maxHeartbeats 1400000 in
private theorem torsion_transport {k : ℕ}
    (φ : (W ⧸ I e) ≃ₜ* (W' ⧸ I' e))
    (hdeg : ∀ w w', φ (π w) = π' w' → d w = d' w')
    (c : ContinuousIrreducibleClasses.TrivialOn.{u, v} (I e) (k + 1)) :
    LocalNumerical.weilTorsionNumber X Ω (k := k)
      (continuousIrreducibleQuotientTransport φ (k + 1) c).val =
      Numerical.weilTorsionNumber F (k := k) c.val := by
  let E := continuousIrreducibleQuotientTransport φ (k + 1)
  have hset :
      {z : ℂˣ | LocalNumerical.weilUnramifiedTwist X Ω k z (E c).val = (E c).val} =
      {z : ℂˣ | Numerical.weilUnramifiedTwist F k z c.val = c.val} := by
    ext z
    obtain ⟨c', hc', hEc'⟩ := unramified_transport F (k := k) φ hdeg c z
    change (LocalNumerical.weilUnramifiedTwist X Ω k z (E c).val = (E c).val) ↔
      (Numerical.weilUnramifiedTwist F k z c.val = c.val)
    rw [← hc', ← hEc']
    constructor
    · intro h
      exact congrArg Subtype.val (E.injective (Subtype.ext h))
    · intro h
      exact congrArg (fun x => (E x).val) (Subtype.ext h)
  exact congrArg (fun S : Set ℂˣ => Nat.card S) hset

open VirtualRepresentation.Weil in
set_option maxHeartbeats 1400000 in
private theorem orbit_eq_iff {k : ℕ}
    (φ : (W ⧸ I e) ≃ₜ* (W' ⧸ I' e))
    (hdeg : ∀ w w', φ (π w) = π' w' → d w = d' w')
    (a b : ContinuousIrreducibleClasses.TrivialOn.{u, v} (I e) (k + 1)) :
    let E := continuousIrreducibleQuotientTransport φ (k + 1)
    unramifiedOrbitClass d ⟨k.succPNat, a.val⟩ =
      unramifiedOrbitClass d ⟨k.succPNat, b.val⟩ ↔
    unramifiedOrbitClass d' ⟨k.succPNat, (E a).val⟩ =
      unramifiedOrbitClass d' ⟨k.succPNat, (E b).val⟩ := by
  let E := continuousIrreducibleQuotientTransport φ (k + 1)
  change _ ↔ unramifiedOrbitClass d' ⟨k.succPNat, (E a).val⟩ =
    unramifiedOrbitClass d' ⟨k.succPNat, (E b).val⟩
  rw [unramifiedOrbitClass_eq_iff, unramifiedOrbitClass_eq_iff]
  change
    (∃ z : ℂˣ, (⟨k.succPNat, Numerical.weilUnramifiedTwist F k z b.val⟩ :
      IrreducibleBasis.{u, v} W) = ⟨k.succPNat, a.val⟩) ↔
    (∃ z : ℂˣ, (⟨k.succPNat, LocalNumerical.weilUnramifiedTwist X Ω k z (E b).val⟩ :
      IrreducibleBasis.{u, v} W') = ⟨k.succPNat, (E a).val⟩)
  apply exists_congr
  intro z
  obtain ⟨b', hb', hEb'⟩ := unramified_transport F (k := k) φ hdeg b z
  rw [← hb', ← hEb']
  constructor
  · intro h
    have hval : b'.val = a.val := (Sigma.mk.inj h).2.eq
    exact congrArg (fun x => (⟨k.succPNat, (E x).val⟩ : IrreducibleBasis.{u, v} W'))
      (Subtype.ext hval)
  · intro h
    have hval : (E b').val = (E a).val := (Sigma.mk.inj h).2.eq
    exact congrArg (fun x => (⟨k.succPNat, x.val⟩ : IrreducibleBasis.{u, v} W))
      (E.injective (Subtype.ext hval))

open VirtualRepresentation.Weil in
set_option maxHeartbeats 1800000 in
private def refinedStratumEquivOfQuotient
    (φ : (W ⧸ I e) ≃ₜ* (W' ⧸ I' e))
    (hφ : ∀ r : ℝ, 0 ≤ r → r ≤ e →
      ((I r).map π).map φ.toMulEquiv.toMonoidHom = (I' r).map π')
    (hdeg : ∀ w w', φ (π w) = π' w' → d w = d' w')
    (k s f : ℕ) (hs : s < (k + 1) * F.canonicalTopologicalData.ramificationIndex) :
    Numerical.weilRefinedStratum.{u, v} F k s f ≃
      LocalNumerical.weilRefinedStratum.{u, u, v} X Ω k s f := by
  let E := continuousIrreducibleQuotientTransport φ (k + 1)
  let A := {c : ContinuousIrreducibleClasses.TrivialOn.{u, v} (I e) (k + 1) //
    Numerical.HasWeilSwan F c.val s ∧ Numerical.weilTorsionNumber F (k := k) c.val = f}
  let toF (c : A) : Numerical.weilRefinedStratum.{u, v} F k s f :=
    ⟨unramifiedOrbitClass d ⟨k.succPNat, c.val.val⟩, ⟨c.val.val, rfl, c.property⟩⟩
  let toX (c : A) : LocalNumerical.weilRefinedStratum.{u, u, v} X Ω k s f :=
    ⟨unramifiedOrbitClass d' ⟨k.succPNat, (E c.val).val⟩,
      ⟨(E c.val).val, rfl, (swan_transport_iff F (k := k) φ hφ c.val).mpr c.property.1,
        (torsion_transport F (k := k) φ hdeg c.val).trans c.property.2⟩⟩
  refine equivOfSameFibers toF toX ?_ ?_ ?_
  · rintro ⟨x, c, hcx, hcs, hcf⟩
    exact ⟨⟨⟨c, padic_trivialOn_of_swan F c hcs hs⟩, hcs, hcf⟩, Subtype.ext hcx⟩
  · rintro ⟨x, c, hcx, hcs, hcf⟩
    let b : ContinuousIrreducibleClasses.TrivialOn.{u, v} (I' e) (k + 1) :=
      ⟨c, laurent_trivialOn_of_swan F c hcs hs⟩
    let a := E.symm b
    have hab : E a = b := E.apply_symm_apply b
    have hsa : Numerical.HasWeilSwan F a.val s := by
      apply (swan_transport_iff F (k := k) φ hφ a).mp
      change LocalNumerical.HasWeilSwan X Ω (E a).val s
      rw [hab]
      exact hcs
    have hfa : Numerical.weilTorsionNumber F (k := k) a.val = f := by
      rw [← torsion_transport F (k := k) φ hdeg a]
      change LocalNumerical.weilTorsionNumber X Ω (k := k) (E a).val = f
      rw [hab]
      exact hcf
    refine ⟨⟨a, hsa, hfa⟩, Subtype.ext ?_⟩
    change unramifiedOrbitClass d' ⟨k.succPNat, (E a).val⟩ = x
    rw [hab]
    exact hcx
  · intro a b
    have heq := orbit_eq_iff F φ hdeg a.val b.val
    constructor
    · intro h
      exact Subtype.ext (heq.mp (congrArg Subtype.val h))
    · intro h
      exact Subtype.ext (heq.mpr (congrArg Subtype.val h))

set_option maxHeartbeats 1400000 in
/-- The refined Weil orbit strata of close fields agree below the absolute
ramification cutoff, with rank, Swan exponent and torsion number fixed. -/
def closeFieldsWeilRefinedStratumEquiv
    (k s f : ℕ) (hs : s < (k + 1) * F.canonicalTopologicalData.ramificationIndex) :
    Numerical.weilRefinedStratum.{u, v} F k s f ≃
      LocalNumerical.weilRefinedStratum.{u, u, v} X Ω k s f := by
  have h : ∃ φ : (W ⧸ I e) ≃ₜ* (W' ⧸ I' e),
      (∀ r : ℝ, 0 ≤ r → r ≤ e → ((I r).map π).map φ.toMulEquiv.toMonoidHom = (I' r).map π') ∧
        ∀ w w', φ (π w) = π' w' → d w = d' w' :=
    Ramification.Local.closeFieldsWeilQuotient p F
  exact refinedStratumEquivOfQuotient F h.choose h.choose_spec.1 h.choose_spec.2 k s f hs

theorem closeFieldsWeilRefinedStratum_encard
    (k s f : ℕ) (hs : s < (k + 1) * F.canonicalTopologicalData.ramificationIndex) :
    (Numerical.weilRefinedStratum.{u, v} F k s f).encard =
      (LocalNumerical.weilRefinedStratum.{u, u, v} X Ω k s f).encard :=
  Set.encard_congr (closeFieldsWeilRefinedStratumEquiv F k s f hs)

/-- The torsion-number-one counts of close fields agree in the strict
ramification range. -/
theorem closeFieldsWeilTwistIrreducibleCount
    (k s : ℕ) (hs : s < (k + 1) * F.canonicalTopologicalData.ramificationIndex) :
    Numerical.weilTwistIrreducibleCount.{u, v} F k s =
      LocalNumerical.weilTwistIrreducibleCount.{u, u, v} X Ω k s :=
  closeFieldsWeilRefinedStratum_encard F k s 1 hs

end Langlands.Henniart
