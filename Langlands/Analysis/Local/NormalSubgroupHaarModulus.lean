import Langlands.Analysis.Local.QuotientAutomorphismProof
import Langlands.Analysis.Local.QuotientMeasureExistence

/-!
# Haar moduli across a closed normal subgroup

A continuous automorphism `α` of a unimodular locally compact group `G` that preserves a
closed unimodular normal subgroup `H` descends to the quotient group `G ⧸ H`. Its Haar
modulus is the product of the moduli of its restriction to `H` and of the induced
automorphism of `G ⧸ H`.
-/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- For a normal subgroup the actual left-coset space `H \ G` is the quotient group. -/
def normalLeftQuotientHomeomorph (H : Subgroup G) [H.Normal] : LeftQuotient H ≃ₜ G ⧸ H :=
  Homeomorph.Quotient.congr (Homeomorph.refl G) (by
    intro x y
    change QuotientGroup.rightRel H x y ↔ QuotientGroup.leftRel H x y
    rw [QuotientGroup.rightRel_apply, QuotientGroup.leftRel_apply]
    exact Subgroup.Normal.mem_comm_iff inferInstance)

omit [IsTopologicalGroup G] in
@[simp] theorem normalLeftQuotientHomeomorph_mk (H : Subgroup G) [H.Normal] (g : G) :
    normalLeftQuotientHomeomorph H (Quotient.mk _ g) = (g : G ⧸ H) := rfl

/-- The automorphism of the quotient group induced by a continuous automorphism
preserving the normal subgroup. -/
def quotientGroupAutomorphism (H : Subgroup G) [H.Normal] (α : G ≃ₜ* G)
    (hα : ∀ x : G, α x ∈ H ↔ x ∈ H) : (G ⧸ H) ≃ₜ* (G ⧸ H) where
  toMulEquiv := QuotientGroup.congr H H α.toMulEquiv (by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hα y).2 hy
    · intro hx
      refine ⟨α.symm x, (hα _).1 ?_, ?_⟩
      · simpa using hx
      · exact α.apply_symm_apply x)
  continuous_toFun := by
    refine (QuotientGroup.isQuotientMap_mk H).continuous_iff.2 ?_
    exact QuotientGroup.continuous_mk.comp α.continuous
  continuous_invFun := by
    refine (QuotientGroup.isQuotientMap_mk H).continuous_iff.2 ?_
    exact QuotientGroup.continuous_mk.comp α.symm.continuous

omit [IsTopologicalGroup G] in
@[simp] theorem quotientGroupAutomorphism_mk (H : Subgroup G) [H.Normal] (α : G ≃ₜ* G)
    (hα : ∀ x : G, α x ∈ H ↔ x ∈ H) (g : G) :
    quotientGroupAutomorphism H α hα (g : G ⧸ H) = ((α g : G) : G ⧸ H) := rfl

/-- Two positive multiples of a nonzero locally finite measure agree only for equal factors. -/
private theorem nnreal_eq_of_smul_eq {X : Type*} [MeasurableSpace X] (ρ : Measure X)
    {s : Set X} (hs0 : ρ s ≠ 0) (hsT : ρ s ≠ ∞) {a b : ℝ≥0} (h : a • ρ = b • ρ) : a = b := by
  have h' := congrArg (fun m : Measure X => m s) h
  simp only [Measure.smul_apply, nnreal_smul_coe_apply] at h'
  exact_mod_cast (ENNReal.mul_left_inj hs0 hsT).1 h'

/-- **Haar moduli are multiplicative across a closed normal subgroup.** For a unimodular
locally compact Hausdorff group `G`, a closed unimodular normal subgroup `H` and a continuous
automorphism `α` of `G` preserving `H`, the Haar modulus of `α` is the product of the moduli of
its restriction to `H` and of the induced automorphism of `G ⧸ H`. -/
theorem mulEquivHaarChar_eq_mul_quotientGroupAutomorphism
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) [H.Normal] (hH : IsClosed (H : Set G))
    [MeasurableSpace H] [BorelSpace H] [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)]
    (μG : Measure G) (μH : Measure H)
    [IsHaarMeasure μG] [μG.Regular] [IsMulRightInvariant μG]
    [IsHaarMeasure μH] [μH.Regular] [IsMulRightInvariant μH]
    (α : G ≃ₜ* G) (hα : ∀ x : G, α x ∈ H ↔ x ∈ H) :
    have : LocallyCompactSpace H := hH.locallyCompactSpace
    mulEquivHaarChar α =
      mulEquivHaarChar (subgroupAutomorphism H α hα) *
        mulEquivHaarChar (quotientGroupAutomorphism H α hα) := by
  have : LocallyCompactSpace H := hH.locallyCompactSpace
  have : IsClosed (H : Set G) := hH
  let _ : MeasurableSpace (LeftQuotient H) := borel _
  have : BorelSpace (LeftQuotient H) := ⟨rfl⟩
  obtain ⟨ν, hν⟩ := compatibleMeasureExists H hH μG μH
  have hmap := hν.map_quotientAutomorphism H hH α hα
  set δG := mulEquivHaarChar α
  set δH := mulEquivHaarChar (subgroupAutomorphism H α hα)
  set δQ := mulEquivHaarChar (quotientGroupAutomorphism H α hα)
  let e := normalLeftQuotientHomeomorph H
  let αQ := quotientGroupAutomorphism H α hα
  let νQ : Measure (G ⧸ H) := ν.map e
  have he : Measurable e := e.continuous.measurable
  have hcomm : (αQ : G ⧸ H → G ⧸ H) ∘ e = e ∘ quotientAutomorphism H α hα := by
    funext q
    induction q using Quotient.inductionOn with
    | h g => rfl
  -- The transported measure is right invariant.
  have hright : IsMulRightInvariant νQ := by
    refine ⟨fun q => ?_⟩
    induction q using QuotientGroup.induction_on with
    | H g =>
      have hc : (fun x : G ⧸ H => x * (g : G ⧸ H)) ∘ e = e ∘ rightTranslate H g := by
        funext q
        induction q using Quotient.inductionOn with
        | h x => rfl
      change Measure.map (fun x : G ⧸ H => x * (g : G ⧸ H)) (ν.map e) = ν.map e
      rw [Measure.map_map (measurable_mul_const _) he, hc,
        ← Measure.map_map he (rightTranslate H g).continuous.measurable,
        (hν.right_invariant g).map_eq]
  have : ν.Regular := hν.regular
  have : νQ.Regular := Measure.Regular.map e
  have hνQ0 : νQ ≠ 0 := by
    intro h0
    apply hν.nonzero
    have := congrArg (fun m : Measure (G ⧸ H) => m.map e.symm) h0
    simp only [Measure.map_zero] at this
    rwa [Measure.map_map e.symm.continuous.measurable he, show (e.symm ∘ e) = id from
      funext e.symm_apply_apply, Measure.map_id] at this
  -- The inverse of the transported measure is a regular left Haar measure.
  let lamQ : Measure (G ⧸ H) := νQ.inv
  have : lamQ.Regular := Measure.Regular.inv
  have : NeZero lamQ := ⟨fun h0 => hνQ0 (by
    have h1 := congrArg Measure.inv h0
    rw [show lamQ.inv = νQ from Measure.inv_inv νQ] at h1
    simpa only [Measure.inv, Measure.map_zero] using h1)⟩
  have : IsHaarMeasure lamQ := { }
  -- Pushforwards.
  have hmapQ : νQ.map αQ = ((δH / δG : ℝ≥0) : ℝ≥0∞) • νQ := by
    change Measure.map αQ (Measure.map e ν) = _
    have hαQ : Measurable (αQ : G ⧸ H → G ⧸ H) := αQ.continuous.measurable
    rw [Measure.map_map hαQ he, hcomm,
      ← Measure.map_map he (quotientAutomorphism H α hα).continuous.measurable, hmap,
      Measure.map_smul _ he.aemeasurable]
  have hmapLam : lamQ.map αQ = (δH / δG) • lamQ := by
    change (νQ.inv).map αQ = (δH / δG) • νQ.inv
    have hαQ : Measurable (αQ : G ⧸ H → G ⧸ H) := αQ.continuous.measurable
    have hinv : (νQ.inv).map αQ = (νQ.map αQ).inv := by
      rw [Measure.inv, Measure.inv, Measure.map_map hαQ measurable_inv,
        Measure.map_map measurable_inv hαQ]
      congr 1
      funext x
      simp [map_inv]
    rw [hinv, hmapQ, Measure.inv, Measure.map_smul _ measurable_inv.aemeasurable]
    rfl
  have hscale := mulEquivHaarChar_smul_map lamQ αQ
  rw [hmapLam, smul_smul] at hscale
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G ⧸ H)
  have hK0 : lamQ K ≠ 0 := (measure_pos_of_mem_nhds lamQ hK1).ne'
  have hKT : lamQ K ≠ ∞ := hK.measure_lt_top.ne
  have hprod : δQ * (δH / δG) = 1 :=
    nnreal_eq_of_smul_eq lamQ hK0 hKT (by rw [hscale, one_smul])
  have hδG : δG ≠ 0 := (mulEquivHaarChar_pos α).ne'
  have hδH : δH ≠ 0 := (mulEquivHaarChar_pos _).ne'
  field_simp at hprod
  rw [← hprod, mul_comm]

end Langlands.QuotientIntegration
