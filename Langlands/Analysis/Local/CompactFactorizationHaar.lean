import Langlands.Analysis.Local.QuotientInvariantComparison
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular

/-!
# Haar measure on a group factored as `G = Q K` with `K` compact

For a second countable locally compact group `G`, a closed subgroup `Q` and a compact subgroup
`K` with `G = Q K`, a left Haar measure on `G` is a positive multiple of the pushforward of
`μQ × μK` under `(q, k) ↦ q k`. As a consequence, the Haar measure of a set saturated by right
multiplication by `K` is a fixed positive multiple of the left Haar measure of its trace on `Q`.
-/

noncomputable section

namespace Langlands.CompactFactorization

open MeasureTheory MeasureTheory.Measure Set Topology Langlands.QuotientIntegration
open scoped NNReal ENNReal Pointwise

universe u

section RightInvariance

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- A regular left Haar measure is invariant under right translation by every element of a
compact subgroup. -/
theorem map_mul_right_eq_self_of_mem (μ : Measure G) [IsHaarMeasure μ] [μ.Regular]
    (K : Subgroup G) (hK : IsCompact (K : Set G)) {k : G} (hk : k ∈ K) :
    Measure.map (· * k) μ = μ := by
  have : (Measure.map (· * k) μ).Regular := Measure.Regular.map (Homeomorph.mulRight k)
  have hc : Measure.map (· * k) μ = haarScalarFactor (Measure.map (· * k) μ) μ • μ :=
    isMulLeftInvariant_eq_smul_of_regular _ μ
  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : G)
  have hCc : IsCompact (V * (K : Set G)) := hVc.mul hK
  have hCK : (· * k) ⁻¹' (V * (K : Set G)) = V * (K : Set G) := by
    ext x
    simp only [mem_preimage, mem_mul, SetLike.mem_coe]
    constructor
    · rintro ⟨v, hv, k', hk', hx⟩
      exact ⟨v, hv, k' * k⁻¹, K.mul_mem hk' (K.inv_mem hk), by rw [← mul_assoc, hx,
        mul_inv_cancel_right]⟩
    · rintro ⟨v, hv, k', hk', hx⟩
      exact ⟨v, hv, k' * k, K.mul_mem hk' hk, by rw [← mul_assoc, hx]⟩
  have hpos : μ (V * (K : Set G)) ≠ 0 :=
    (measure_pos_of_mem_nhds μ (Filter.mem_of_superset hV1
      (subset_mul_left V K.one_mem))).ne'
  have hfin : μ (V * (K : Set G)) ≠ ∞ := hCc.measure_lt_top.ne
  have h1 : Measure.map (· * k) μ (V * (K : Set G)) = μ (V * (K : Set G)) := by
    rw [map_apply (measurable_mul_const k) hCc.measurableSet, hCK]
  rw [hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h1
  have h2 : (haarScalarFactor (Measure.map (· * k) μ) μ : ℝ≥0∞) = 1 :=
    (ENNReal.mul_eq_right hpos hfin).mp h1
  rw [hc, show haarScalarFactor (Measure.map (· * k) μ) μ = 1 by exact_mod_cast h2, one_smul]

/-- A Haar measure on a compact group is right invariant. -/
theorem isMulRightInvariant_of_compactSpace [CompactSpace G] (μ : Measure G) [IsHaarMeasure μ] :
    IsMulRightInvariant μ :=
  ⟨fun k => map_mul_right_eq_self_of_mem μ ⊤ (by simpa using isCompact_univ) (Subgroup.mem_top k)⟩

end RightInvariance

section Diagonal

variable {G : Type u} [Group G]

/-- The diagonal copy of `Q ∩ K` inside `Q × K`. -/
def diagonalSubgroup (Q K : Subgroup G) : Subgroup (Q × K) where
  carrier := {p | (p.1 : G) = p.2}
  mul_mem' {a b} ha hb := by
    simp only [mem_ofPred_eq, Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul] at *
    rw [ha, hb]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [mem_ofPred_eq, Prod.fst_inv, Prod.snd_inv, Subgroup.coe_inv] at *
    rw [ha]

@[simp] theorem mem_diagonalSubgroup (Q K : Subgroup G) {p : Q × K} :
    p ∈ diagonalSubgroup Q K ↔ (p.1 : G) = p.2 := Iff.rfl

/-- The map `(q, k) ↦ q⁻¹ k`, which is constant on the cosets of the diagonal subgroup. -/
def factorMap (Q K : Subgroup G) : LeftQuotient (diagonalSubgroup Q K) → G :=
  descend _ (fun p : Q × K => (p.1 : G)⁻¹ * p.2) (by
    rintro ⟨⟨h₁, h₂⟩, hh⟩ ⟨q, k⟩
    rw [mem_diagonalSubgroup] at hh
    simp only [Prod.mk_mul_mk, Subgroup.coe_mul, mul_inv_rev]
    rw [hh, mul_assoc, inv_mul_cancel_left])

@[simp] theorem factorMap_mk (Q K : Subgroup G) (p : Q × K) :
    factorMap Q K (Quotient.mk _ p) = (p.1 : G)⁻¹ * p.2 := rfl

theorem factorMap_injective (Q K : Subgroup G) : Function.Injective (factorMap Q K) := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | h p =>
  induction y using Quotient.inductionOn with
  | h p' =>
  rw [factorMap_mk, factorMap_mk] at hxy
  refine Quotient.sound (QuotientGroup.rightRel_apply.mpr ?_)
  rw [mem_diagonalSubgroup]
  simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv, Subgroup.coe_mul,
    Subgroup.coe_inv]
  calc (p'.1 : G) * (p.1 : G)⁻¹ = (p'.1 : G) * ((p.1 : G)⁻¹ * p.2) * (p.2 : G)⁻¹ := by group
    _ = (p'.1 : G) * ((p'.1 : G)⁻¹ * p'.2) * (p.2 : G)⁻¹ := by rw [hxy]
    _ = (p'.2 : G) * (p.2 : G)⁻¹ := by group

theorem factorMap_surjective (Q K : Subgroup G) (hQK : ∀ g : G, ∃ q ∈ Q, ∃ k ∈ K, g = q * k) :
    Function.Surjective (factorMap Q K) := by
  intro g
  obtain ⟨q, hq, k, hk, rfl⟩ := hQK g
  exact ⟨Quotient.mk _ (⟨q⁻¹, Q.inv_mem hq⟩, ⟨k, hk⟩), by simp⟩

theorem factorMap_rightTranslate [TopologicalSpace G] [IsTopologicalGroup G]
    (Q K : Subgroup G) (p : Q × K) (x : LeftQuotient (diagonalSubgroup Q K)) :
    factorMap Q K (rightTranslate _ p x) = (p.1 : G)⁻¹ * factorMap Q K x * p.2 := by
  induction x using Quotient.inductionOn with
  | h x =>
  rw [rightTranslate_mk, factorMap_mk, factorMap_mk]
  simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, mul_inv_rev, mul_assoc]

end Diagonal

section Homeomorph

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G]
variable {Q K : Subgroup G}

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] in
theorem isClosed_diagonalSubgroup (Q K : Subgroup G) :
    IsClosed (diagonalSubgroup Q K : Set (Q × K)) :=
  isClosed_eq (continuous_subtype_val.comp continuous_fst)
    (continuous_subtype_val.comp continuous_snd)

omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] in
theorem continuous_factorMap (Q K : Subgroup G) : Continuous (factorMap Q K) :=
  Continuous.quotient_lift (((continuous_subtype_val.comp continuous_fst).inv).mul
    (continuous_subtype_val.comp continuous_snd)) _

theorem isOpenMap_factorMap (hQ : IsClosed (Q : Set G)) (hK : IsCompact (K : Set G))
    (hQK : ∀ g : G, ∃ q ∈ Q, ∃ k ∈ K, g = q * k) : IsOpenMap (factorMap Q K) := by
  have : LocallyCompactSpace Q := hQ.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : SecondCountableTopology Q := inferInstanceAs (SecondCountableTopology (Q : Set G))
  let act : MulAction (Q × K) G :=
    { smul := fun p g => (p.1 : G) * g * (p.2 : G)⁻¹
      one_smul := fun g => by
        change ((1 : Q × K).1 : G) * g * ((1 : Q × K).2 : G)⁻¹ = g
        simp
      mul_smul := fun p p' g => by
        change ((p * p').1 : G) * g * ((p * p').2 : G)⁻¹ =
          (p.1 : G) * ((p'.1 : G) * g * (p'.2 : G)⁻¹) * (p.2 : G)⁻¹
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, mul_inv_rev, mul_assoc] }
  have hsmul : ∀ (p : Q × K) (g : G), p • g = (p.1 : G) * g * (p.2 : G)⁻¹ := fun _ _ => rfl
  have : ContinuousSMul (Q × K) G := ⟨by
    simp only [hsmul]
    fun_prop⟩
  have : MulAction.IsPretransitive (Q × K) G := ⟨fun x y => by
    obtain ⟨q, hq, k, hk, rfl⟩ := hQK x
    obtain ⟨q', hq', k', hk', rfl⟩ := hQK y
    refine ⟨(⟨q' * q⁻¹, Q.mul_mem hq' (Q.inv_mem hq)⟩, ⟨k'⁻¹ * k, K.mul_mem (K.inv_mem hk') hk⟩), ?_⟩
    rw [hsmul]
    simp only
    group⟩
  have hopen : IsOpenMap (fun p : Q × K => p • (1 : G)) := isOpenMap_smul_of_sigmaCompact 1
  intro U hU
  have himage : factorMap Q K '' U =
      (fun p : Q × K => p • (1 : G)) '' ((fun p : Q × K => p⁻¹) ⁻¹'
        (Quotient.mk (QuotientGroup.rightRel (diagonalSubgroup Q K)) ⁻¹' U)) := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      induction x using Quotient.inductionOn with
      | h p =>
      refine ⟨p⁻¹, by simpa using hx, ?_⟩
      simp only [hsmul, factorMap_mk, Prod.fst_inv, Prod.snd_inv, Subgroup.coe_inv, inv_inv,
        mul_one]
    · rintro ⟨p, hp, rfl⟩
      refine ⟨Quotient.mk _ p⁻¹, hp, ?_⟩
      simp only [hsmul, factorMap_mk, Prod.fst_inv, Prod.snd_inv, Subgroup.coe_inv, inv_inv,
        mul_one]
  rw [himage]
  exact hopen _ ((hU.preimage continuous_quotient_mk').preimage continuous_inv)

/-- The coset space `(Q × K) / diag(Q ∩ K)` is homeomorphic to `G` through `(q, k) ↦ q⁻¹ k`. -/
def factorHomeomorph (hQ : IsClosed (Q : Set G)) (hK : IsCompact (K : Set G))
    (hQK : ∀ g : G, ∃ q ∈ Q, ∃ k ∈ K, g = q * k) :
    LeftQuotient (diagonalSubgroup Q K) ≃ₜ G :=
  (Equiv.ofBijective (factorMap Q K)
    ⟨factorMap_injective Q K, factorMap_surjective Q K hQK⟩).toHomeomorphOfContinuousOpen
    (continuous_factorMap Q K) (isOpenMap_factorMap hQ hK hQK)

@[simp] theorem factorHomeomorph_apply (hQ : IsClosed (Q : Set G)) (hK : IsCompact (K : Set G))
    (hQK : ∀ g : G, ∃ q ∈ Q, ∃ k ∈ K, g = q * k) (x : LeftQuotient (diagonalSubgroup Q K)) :
    factorHomeomorph hQ hK hQK x = factorMap Q K x := rfl

end Homeomorph

section Measure

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- **Haar measure on `G = Q K`.** Let `Q` be a closed subgroup and `K` a compact subgroup of a
second countable locally compact group `G` with `G = Q K`. Then every left Haar measure on `G` is
a positive multiple of the pushforward of `μQ × μK` under `(q, k) ↦ q k`, for any left Haar
measures `μQ` on `Q` and `μK` on `K`. -/
theorem exists_pos_eq_smul_map_mul_prod (μ : Measure G) [IsHaarMeasure μ]
    (Q : Subgroup G) (hQ : IsClosed (Q : Set G)) (K : Subgroup G) (hK : IsCompact (K : Set G))
    (hQK : ∀ g : G, ∃ q ∈ Q, ∃ k ∈ K, g = q * k)
    (μQ : Measure Q) [IsHaarMeasure μQ] (μK : Measure K) [IsHaarMeasure μK] :
    ∃ c : ℝ≥0, 0 < c ∧ μ = c • Measure.map (fun p : Q × K => (p.1 : G) * p.2) (μQ.prod μK) := by
  have : LocallyCompactSpace Q := hQ.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : SecondCountableTopology Q := inferInstanceAs (SecondCountableTopology (Q : Set G))
  have : SecondCountableTopology K := inferInstanceAs (SecondCountableTopology (K : Set G))
  have : BorelSpace Q := inferInstanceAs (BorelSpace (Q : Set G))
  have : BorelSpace K := inferInstanceAs (BorelSpace (K : Set G))
  set H := diagonalSubgroup Q K
  have hH : IsClosed (H : Set (Q × K)) := isClosed_diagonalSubgroup Q K
  have hHc : IsCompact (H : Set (Q × K)) := by
    have hQK' : IsCompact (((Subtype.val : Q → G) ⁻¹' (K : Set G)) ×ˢ (univ : Set K)) :=
      (hQ.isClosedEmbedding_subtypeVal.isCompact_preimage hK).prod isCompact_univ
    refine hQK'.of_isClosed_subset hH ?_
    rintro ⟨q, k⟩ hp
    rw [SetLike.mem_coe, mem_diagonalSubgroup] at hp
    simp only at hp
    refine ⟨?_, mem_univ _⟩
    change (q : G) ∈ K
    rw [hp]
    exact k.2
  have : CompactSpace H := isCompact_iff_compactSpace.mp hHc
  let μH : Measure H := Measure.haar
  have : IsMulRightInvariant μH := isMulRightInvariant_of_compactSpace μH
  have : IsMulRightInvariant μK := isMulRightInvariant_of_compactSpace μK
  let : MeasurableSpace (LeftQuotient H) := borel _
  have : BorelSpace (LeftQuotient H) := ⟨rfl⟩
  let e := factorHomeomorph hQ hK hQK
  set Ψ : Q × K → G := fun p => (p.1 : G) * p.2 with hΨ
  have hΨc : Continuous Ψ :=
    (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  set ν := Measure.map Ψ (μQ.prod μK) with hν
  -- the twisted translations `g ↦ q⁻¹ g k`
  have hφ : ∀ p : Q × K, Measurable (fun g : G => (p.1 : G)⁻¹ * g * p.2) := fun p =>
    (measurable_const_mul _).mul_const _
  -- Transport of an invariant measure on `G` to the quotient.
  have htrans : ∀ ρ : Measure G,
      (∀ p : Q × K, Measure.map (fun g : G => (p.1 : G)⁻¹ * g * p.2) ρ = ρ) →
      ∀ p : Q × K, MeasurePreserving (rightTranslate H p) (Measure.map e.symm ρ)
        (Measure.map e.symm ρ) := by
    intro ρ hρ p
    refine ⟨(rightTranslate H p).continuous.measurable, ?_⟩
    have hcomm : (rightTranslate H p) ∘ e.symm =
        e.symm ∘ (fun g : G => (p.1 : G)⁻¹ * g * p.2) := by
      funext g
      apply e.injective
      simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
      rw [factorHomeomorph_apply, factorMap_rightTranslate, ← factorHomeomorph_apply hQ hK hQK,
        Homeomorph.apply_symm_apply]
    rw [Measure.map_map (rightTranslate H p).continuous.measurable e.symm.continuous.measurable,
      hcomm, ← Measure.map_map e.symm.continuous.measurable (hφ p), hρ p]
  have hback : ∀ ρ : Measure G, Measure.map e (Measure.map e.symm ρ) = ρ := fun ρ => by
    rw [Measure.map_map e.continuous.measurable e.symm.continuous.measurable,
      Homeomorph.self_comp_symm, Measure.map_id]
  -- invariance of `μ`
  have hμinv : ∀ p : Q × K, Measure.map (fun g : G => (p.1 : G)⁻¹ * g * p.2) μ = μ := by
    intro p
    have : (fun g : G => (p.1 : G)⁻¹ * g * p.2) = (· * (p.2 : G)) ∘ ((p.1 : G)⁻¹ * ·) := rfl
    rw [this, ← Measure.map_map (measurable_mul_const _) (measurable_const_mul _),
      map_mul_left_eq_self, map_mul_right_eq_self_of_mem μ K hK p.2.2]
  -- invariance of `ν`
  have hνinv : ∀ p : Q × K, Measure.map (fun g : G => (p.1 : G)⁻¹ * g * p.2) ν = ν := by
    intro p
    have hcomp : (fun g : G => (p.1 : G)⁻¹ * g * p.2) ∘ Ψ =
        Ψ ∘ Prod.map (fun q : Q => p.1⁻¹ * q) (fun k : K => k * p.2) := by
      funext x
      simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, hΨ, Subgroup.coe_mul,
        Subgroup.coe_inv, mul_assoc]
    rw [hν, Measure.map_map (hφ p) hΨc.measurable, hcomp,
      ← Measure.map_map hΨc.measurable ((measurable_const_mul _).prodMap (measurable_mul_const _)),
      ← Measure.map_prod_map _ _ (measurable_const_mul _) (measurable_mul_const _),
      map_mul_left_eq_self, map_mul_right_eq_self]
  -- `ν` is finite on compact sets and nonzero
  have : IsFiniteMeasureOnCompacts ν := ⟨fun C hC => by
    rw [hν, Measure.map_apply hΨc.measurable hC.measurableSet]
    have hA : IsCompact ((Subtype.val : Q → G) ⁻¹' (C * (K : Set G))) :=
      hQ.isClosedEmbedding_subtypeVal.isCompact_preimage (hC.mul hK)
    calc (μQ.prod μK) (Ψ ⁻¹' C)
        ≤ (μQ.prod μK) (((Subtype.val : Q → G) ⁻¹' (C * (K : Set G))) ×ˢ (univ : Set K)) := by
          refine measure_mono ?_
          rintro ⟨q, k⟩ hx
          refine ⟨?_, mem_univ _⟩
          simp only [mem_preimage, hΨ] at hx ⊢
          exact ⟨(q : G) * k, hx, (k : G)⁻¹, K.inv_mem k.2, mul_inv_cancel_right _ _⟩
      _ = μQ ((Subtype.val : Q → G) ⁻¹' (C * (K : Set G))) * μK univ := Measure.prod_prod _ _
      _ < ∞ := ENNReal.mul_lt_top hA.measure_lt_top (measure_lt_top μK univ)⟩
  have hν0 : ν ≠ 0 := by
    intro h0
    have h1 : ν univ = 0 := by rw [h0, Measure.coe_zero, Pi.zero_apply]
    rw [hν, Measure.map_apply hΨc.measurable MeasurableSet.univ, preimage_univ,
      ← univ_prod_univ, Measure.prod_prod] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact (IsOpenPosMeasure.open_pos univ isOpen_univ univ_nonempty) h
    · exact (IsOpenPosMeasure.open_pos univ isOpen_univ univ_nonempty) h
  have hμ0 : μ ≠ 0 := NeZero.ne μ
  -- comparison on the quotient
  have hreg₁ : (Measure.map e.symm μ).Regular := Measure.Regular.map e.symm
  have hreg₂ : (Measure.map e.symm ν).Regular := Measure.Regular.map e.symm
  have hne₁ : Measure.map e.symm μ ≠ 0 := by
    rw [Ne, Measure.map_eq_zero_iff e.symm.continuous.measurable.aemeasurable]; exact hμ0
  have hne₂ : Measure.map e.symm ν ≠ 0 := by
    rw [Ne, Measure.map_eq_zero_iff e.symm.continuous.measurable.aemeasurable]; exact hν0
  obtain ⟨C, hC, hEq⟩ := exists_pos_smul_eq_of_rightInvariant_quotient H hH μH
    (Measure.map e.symm μ) (Measure.map e.symm ν) hne₁ hne₂ (htrans μ hμinv) (htrans ν hνinv)
  refine ⟨C.toNNReal, Real.toNNReal_pos.mpr hC, ?_⟩
  have := congrArg (Measure.map e) hEq
  rw [hback, Measure.map_smul, hback, ENNReal.ofReal] at this
  · rw [this, ENNReal.smul_def]
  · exact e.continuous.measurable.aemeasurable

/-- **Haar measure of a right `K`-saturated set.** In the situation of
`exists_pos_eq_smul_map_mul_prod`, there is a positive constant `c` such that every measurable
set `A ⊆ G` with `A K = A` has Haar measure `c` times the left Haar measure of `A ∩ Q`. -/
theorem exists_pos_measure_eq_of_mul_mem (μ : Measure G) [IsHaarMeasure μ]
    (Q : Subgroup G) (hQ : IsClosed (Q : Set G)) (K : Subgroup G) (hK : IsCompact (K : Set G))
    (hQK : ∀ g : G, ∃ q ∈ Q, ∃ k ∈ K, g = q * k) (μQ : Measure Q) [IsHaarMeasure μQ] :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ A : Set G, MeasurableSet A → (∀ a ∈ A, ∀ k ∈ K, a * k ∈ A) →
      μ A = c * μQ ((Subtype.val : Q → G) ⁻¹' A) := by
  have : LocallyCompactSpace Q := hQ.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : SecondCountableTopology Q := inferInstanceAs (SecondCountableTopology (Q : Set G))
  have : SecondCountableTopology K := inferInstanceAs (SecondCountableTopology (K : Set G))
  have : BorelSpace Q := inferInstanceAs (BorelSpace (Q : Set G))
  have : BorelSpace K := inferInstanceAs (BorelSpace (K : Set G))
  let μK : Measure K := Measure.haar
  obtain ⟨c₀, hc₀, hμ⟩ := exists_pos_eq_smul_map_mul_prod μ Q hQ K hK hQK μQ μK
  have hK0 : μK univ ≠ 0 := IsOpenPosMeasure.open_pos univ isOpen_univ univ_nonempty
  have hKtop : μK univ ≠ ∞ := measure_ne_top μK univ
  refine ⟨c₀ * (μK univ).toNNReal, mul_pos hc₀ (ENNReal.toNNReal_pos hK0 hKtop), ?_⟩
  intro A hA hAK
  have hΨ : Measurable (fun p : Q × K => (p.1 : G) * p.2) :=
    ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)).measurable
  have hslice : ∀ k : K, (fun q : Q => (q, k)) ⁻¹' ((fun p : Q × K => (p.1 : G) * p.2) ⁻¹' A) =
      (Subtype.val : Q → G) ⁻¹' A := by
    intro k
    ext q
    simp only [mem_preimage]
    constructor
    · intro h
      simpa using hAK _ h _ (K.inv_mem k.2)
    · intro h
      exact hAK _ h _ k.2
  rw [hμ, Measure.smul_apply, Measure.map_apply hΨ hA, Measure.prod_apply_symm (hΨ hA)]
  simp only [hslice, lintegral_const, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_mul,
    ENNReal.coe_toNNReal hKtop]
  ring

end Measure

end Langlands.CompactFactorization
