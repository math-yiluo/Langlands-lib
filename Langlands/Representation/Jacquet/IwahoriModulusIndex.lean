import Langlands.Representation.Jacquet.IwahoriCellVolume
import Langlands.Group.HaarModulus

/-! # The Haar modulus of a weak contraction is the inverse Iwahori index

For a compact open subgroup `K`, a closed subgroup `N` normalized by `g`, and a
weak contraction `g (K ∩ N) g⁻¹ ⊆ K ∩ N`, the Haar modulus of conjugation by `g`
on `N` is `[K ∩ N : g (K ∩ N) g⁻¹]⁻¹`. Consequently the inverse half character used
in the normalized Jacquet module has squared modulus equal to this index.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal Pointwise

namespace Langlands.Jacquet

universe uG

/-- In a group with a left-invariant measure, a measurable subgroup `H` of finite
index in `L ≥ H` satisfies `[L : H] * μ(H) = μ(L)`. -/
theorem relIndex_mul_measure {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]
    (μ : Measure Γ) [μ.IsMulLeftInvariant] (H L : Subgroup Γ) (hHL : H ≤ L)
    [Finite (↥L ⧸ H.subgroupOf L)] (hH : MeasurableSet (H : Set Γ)) :
    (H.relIndex L : ℝ≥0∞) * μ H = μ L := by
  have hcover : (L : Set Γ) = ⋃ q : ↥L ⧸ H.subgroupOf L, (q.out : Γ) • (H : Set Γ) := by
    ext x
    constructor
    · intro hx
      let q : ↥L ⧸ H.subgroupOf L := QuotientGroup.mk ⟨x, hx⟩
      have hq : (q.out)⁻¹ * ⟨x, hx⟩ ∈ H.subgroupOf L := by
        rw [← QuotientGroup.eq]
        exact Quotient.out_eq' q
      rw [Subgroup.mem_subgroupOf] at hq
      refine Set.mem_iUnion.mpr ⟨q, (q.out : Γ)⁻¹ * x, ?_, by simp⟩
      simpa using hq
    · intro hx
      obtain ⟨q, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
      exact L.mul_mem (q.out).2 (hHL hy)
  have hdisj : Pairwise (Function.onFun Disjoint
      fun q : ↥L ⧸ H.subgroupOf L => (q.out : Γ) • (H : Set Γ)) := by
    intro q q' hqq'
    rw [Function.onFun, Set.disjoint_left]
    rintro _ ⟨y, hy, rfl⟩ ⟨y', hy', hyy'⟩
    apply hqq'
    rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    change (QuotientGroup.mk q.out : ↥L ⧸ H.subgroupOf L) = QuotientGroup.mk q'.out
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have e : ((q.out)⁻¹ * q'.out : ↥L) = (y * y'⁻¹ : Γ) := by
      change (q.out : Γ)⁻¹ * q'.out = y * y'⁻¹
      have : (q'.out : Γ) * y' = q.out * y := hyy'
      calc (q.out : Γ)⁻¹ * q'.out = (q.out : Γ)⁻¹ * (q'.out * y') * y'⁻¹ := by group
        _ = (q.out : Γ)⁻¹ * (q.out * y) * y'⁻¹ := by rw [this]
        _ = y * y'⁻¹ := by group
    rw [e]
    exact H.mul_mem hy (H.inv_mem hy')
  rw [hcover, measure_iUnion hdisj (fun q => hH.const_smul _)]
  simp only [measure_smul]
  rw [ENNReal.tsum_const, ENat.card_eq_coe_natCard, Subgroup.relIndex, Subgroup.index]
  rfl

section Modulus

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {K : OpenSubgroup G} {N : Subgroup G} {g : G}

local instance modulusSubgroupMeasurableSpace (U : Subgroup G) : MeasurableSpace U := borel U
local instance modulusSubgroupBorelSpace (U : Subgroup G) : BorelSpace U := ⟨rfl⟩

/-- The relative finite index of `g (K ∩ N) g⁻¹` in `K ∩ N`, from compactness. -/
theorem iwahoriIndex_ne_zero (hK : IsCompact (K : Set G)) (hN : IsClosed (N : Set G))
    (hgN : g ∈ Subgroup.normalizer (N : Set G)) :
    iwahoriIndex K N g ≠ 0 := by
  have hc : IsCompact (((K.toSubgroup ⊓ N : Subgroup G)) : Set G) := hK.inter_right hN
  have : CompactSpace ↥(K.toSubgroup ⊓ N) := isCompact_iff_compactSpace.mp hc
  have hfin : Finite (↥(K.toSubgroup ⊓ N) ⧸
      (conjRadicalPiece K N g).subgroupOf (K.toSubgroup ⊓ N)) := by
    apply Subgroup.quotient_finite_of_isOpen
    have hopen : IsOpen ((fun x : G => g⁻¹ * x * g) ⁻¹' (K : Set G)) :=
      K.isOpen.preimage (by fun_prop)
    convert hopen.preimage continuous_subtype_val using 1
    ext x
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_preimage]
    exact mem_conjRadicalPiece_iff_of_mem hgN x.2.2
  have hfi : ((conjRadicalPiece K N g).subgroupOf (K.toSubgroup ⊓ N)).FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  exact hfi.index_ne_zero

/-- **Haar modulus of a weak contraction.** If `g` normalizes the closed subgroup
`N` and maps `K ∩ N` into itself, the Haar modulus of conjugation by `g` on `N`
is the inverse of the Iwahori index `[K ∩ N : g (K ∩ N) g⁻¹]`. -/
theorem closedNormalizerCharacter_mul_iwahoriIndex [LocallyCompactSpace G]
    (hK : IsCompact (K : Set G)) (hN : IsClosed (N : Set G))
    (hgN : g ∈ Subgroup.normalizer (N : Set G))
    (hup : ∀ u ∈ K.toSubgroup ⊓ N, g * u * g⁻¹ ∈ K.toSubgroup ⊓ N) :
    (HaarModulus.closedNormalizerCharacter N hN ⟨g, hgN⟩ : ℝ≥0) *
      (iwahoriIndex K N g : ℝ≥0) = 1 := by
  let := hN.locallyCompactSpace
  rw [HaarModulus.closedNormalizerCharacter_eq, HaarModulus.normalizerCharacter_apply]
  let μ : Measure ↥N := Measure.haar
  let φ := HaarModulus.normalizerConj N ⟨g, hgN⟩
  let U' : Subgroup ↥N := (K.toSubgroup ⊓ N).subgroupOf N
  let H' : Subgroup ↥N := (conjRadicalPiece K N g).subgroupOf N
  have hH'U' : H' ≤ U' := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨v, hv, hvx⟩ := mem_conjRadicalPiece.mp hx
    rw [← hvx]
    exact hup v hv
  have hmemH' : ∀ x : ↥N, x ∈ H' ↔ g⁻¹ * (x : G) * g ∈ K := by
    intro x
    rw [Subgroup.mem_subgroupOf]
    exact mem_conjRadicalPiece_iff_of_mem hgN x.2
  have hpre : φ ⁻¹' (H' : Set ↥N) = (U' : Set ↥N) := by
    ext x
    simp only [Set.mem_preimage, SetLike.mem_coe, hmemH', U', Subgroup.mem_subgroupOf]
    change g⁻¹ * (g * (x : G) * g⁻¹) * g ∈ K ↔ (x : G) ∈ K.toSubgroup ⊓ N
    rw [show g⁻¹ * (g * (x : G) * g⁻¹) * g = x by group]
    exact ⟨fun h => ⟨h, x.2⟩, fun h => h.1⟩
  have hH'open : IsOpen (H' : Set ↥N) := by
    have hopen : IsOpen ((fun x : G => g⁻¹ * x * g) ⁻¹' (K : Set G)) :=
      K.isOpen.preimage (by fun_prop)
    convert hopen.preimage continuous_subtype_val using 1
    ext x
    exact hmemH' x
  have hU'compact : IsCompact (U' : Set ↥N) := by
    have hc : IsCompact (((K.toSubgroup ⊓ N : Subgroup G)) : Set G) := hK.inter_right hN
    exact hN.isClosedEmbedding_subtypeVal.isCompact_preimage hc
  have hpos : μ H' ≠ 0 := (hH'open.measure_pos μ ⟨1, H'.one_mem⟩).ne'
  have htop : μ H' ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono hH'U') hU'compact.measure_lt_top).ne
  have hd : iwahoriIndex K N g ≠ 0 := iwahoriIndex_ne_zero hK hN hgN
  have hrel : H'.relIndex U' = iwahoriIndex K N g :=
    Subgroup.relIndex_subgroupOf (inf_le_right)
  have hfi : (H'.subgroupOf U').FiniteIndex := ⟨by
    change H'.relIndex U' ≠ 0
    rw [hrel]
    exact hd⟩
  have hfin : Finite (↥U' ⧸ H'.subgroupOf U') := Subgroup.finite_quotient_of_finiteIndex
  have key1 := mulEquivHaarChar_smul_preimage μ (X := (H' : Set ↥N)) φ
  rw [hpre] at key1
  have key2 := relIndex_mul_measure μ H' U' hH'U' hH'open.measurableSet
  rw [hrel] at key2
  rw [← key2, ENNReal.smul_def, smul_eq_mul, ← mul_assoc] at key1
  have hprod : ((mulEquivHaarChar φ : ℝ≥0∞) * (iwahoriIndex K N g : ℝ≥0∞)) = 1 := by
    have := (ENNReal.mul_eq_right hpos htop).mp key1
    exact this
  have hprod' : (((mulEquivHaarChar φ * (iwahoriIndex K N g : ℝ≥0) : ℝ≥0)) : ℝ≥0∞) = 1 := by
    push_cast
    exact hprod
  exact_mod_cast hprod'

/-- The inverse half character of the normalized Jacquet module has squared
modulus equal to the Iwahori index of a weakly contracting element. -/
theorem norm_closedInverseHalfCharacter_sq [LocallyCompactSpace G]
    (hK : IsCompact (K : Set G)) (hN : IsClosed (N : Set G))
    (M : Subgroup G) (hMN : M ≤ Subgroup.normalizer (N : Set G)) (m : M)
    (hup : ∀ u ∈ K.toSubgroup ⊓ N, (m : G) * u * (m : G)⁻¹ ∈ K.toSubgroup ⊓ N) :
    ‖(HaarModulus.closedInverseHalfCharacter N hN M hMN m : ℂ)‖ ^ 2 =
      (iwahoriIndex K N m : ℝ) := by
  have key := closedNormalizerCharacter_mul_iwahoriIndex hK hN (hMN m.2) hup
  set δ : ℝ≥0 := (HaarModulus.closedNormalizerCharacter N hN ⟨m, hMN m.2⟩ : ℝ≥0) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    exact pos_iff_ne_zero.mpr (Units.ne_zero _)
  rw [HaarModulus.closedInverseHalfCharacter, Jacquet.inverseHalfCharacter_apply]
  change ‖(((NNReal.sqrt δ : ℝ) : ℂ))⁻¹‖ ^ 2 = _
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _),
    inv_pow, ← NNReal.coe_pow, NNReal.sq_sqrt]
  have key' : (δ : ℝ) * (iwahoriIndex K N m : ℝ) = 1 := by exact_mod_cast key
  have hδne : (δ : ℝ) ≠ 0 := by exact_mod_cast hδpos.ne'
  field_simp
  linarith

end Modulus

end Langlands.Jacquet
