import Langlands.HarmonicAnalysis.HarishChandraSchwartz.IwahoriLeviDoubleCosetVolumeStatement
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ContractionHaarIndex
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.LatticeQuotientVolumeBound

/-! # Proof of the Iwahori double-coset volume formula with the Levi index -/

universe u

open MeasureTheory
open scoped ENNReal NNReal Pointwise

namespace Langlands.HarishChandraSchwartz

open BruhatTits.SpecialCompact

variable {G : Type u} [Group G]

private theorem relIndex_eq_of_coset_cover {A B J : Subgroup G} (hAB : A ≤ B)
    (hcover : (B : Set G) ⊆ (A : Set G) * (J : Set G)) :
    J.relIndex B = J.relIndex A := by
  let e := Subgroup.quotientSubgroupOfEmbeddingOfLE J hAB
  have he : Function.Surjective e := by
    intro q
    refine Quotient.inductionOn q ?_
    intro b
    obtain ⟨a, ha, j, hj, hab⟩ := Set.mem_mul.mp (hcover b.property)
    refine ⟨QuotientGroup.mk ⟨a, ha⟩, ?_⟩
    simp only [e, Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq]
    change a⁻¹ * (b : G) ∈ J
    rw [← hab, inv_mul_cancel_left]
    exact hj
  exact Nat.card_congr (Equiv.ofBijective e ⟨e.injective, he⟩).symm

private theorem relIndex_conjSubgroup_inf {K U : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (U : Set G)) :
    (conjSubgroup g K).relIndex (K ⊓ U) =
      (conjSubgroup g (K ⊓ U)).relIndex (K ⊓ U) := by
  apply congrArg Subgroup.index
  ext x
  change (x : G) ∈ conjSubgroup g K ↔ (x : G) ∈ conjSubgroup g (K ⊓ U)
  simp only [mem_conjSubgroup, Subgroup.mem_inf]
  exact (and_iff_left ((Subgroup.mem_normalizer_iff''.mp hg _).mp x.property.2)).symm

private theorem iwahoriDoubleCoset_set_index (K M N Nbar : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer (N : Set G))
    (hMV : M ≤ Subgroup.normalizer (Nbar : Set G)) (m : M)
    (hcell : Function.Injective
      (fun t : Nbar × M × N => (t.1 : G) * (t.2.1 : G) * (t.2.2 : G)))
    (hdec : HasIwahoriIntersectionDecomposition K M N Nbar)
    (hVJ : K ⊓ Nbar ≤ conjSubgroup (m : G) K) :
    DoubleCoset.doubleCoset (m : G) K K =
      ((K ⊓ N : Subgroup G) : Set G) * ((K ⊓ M : Subgroup G) : Set G) *
        {(m : G)} * (K : Set G) ∧
    doubleCosetIndex K m =
      doubleCosetIndex (K ⊓ M) m *
        (conjSubgroup (m : G) (K ⊓ N)).relIndex (K ⊓ N) := by
  let g : G := m
  let KM := K ⊓ M
  let KN := K ⊓ N
  let KV := K ⊓ Nbar
  let J := conjSubgroup g K
  let L := KM ⊔ KN
  let H := (J ⊓ KM) ⊔ KN
  have hKMnorm : KM ≤ Subgroup.normalizer (KN : Set G) :=
    (le_inf (inf_le_left.trans K.le_normalizer) (inf_le_right.trans hMN)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hL_MN : (L : Set G) = (KM : Set G) * (KN : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right KM KN hKMnorm
  have hL_NM : (L : Set G) = (KN : Set G) * (KM : Set G) :=
    hL_MN.trans (Subgroup.set_mul_normalizer_comm KM KN hKMnorm)
  have hHnorm : J ⊓ KM ≤ Subgroup.normalizer (KN : Set G) :=
    inf_le_right.trans hKMnorm
  have hH_MN : (H : Set G) = ((J ⊓ KM : Subgroup G) : Set G) * (KN : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right (J ⊓ KM) KN hHnorm
  have hH_NM : (H : Set G) = (KN : Set G) * ((J ⊓ KM : Subgroup G) : Set G) :=
    hH_MN.trans (Subgroup.set_mul_normalizer_comm (J ⊓ KM : Subgroup G) KN hHnorm)
  have hLK : L ≤ K := sup_le inf_le_left inf_le_left
  have hHL : H ≤ L := sup_le (inf_le_right.trans le_sup_left) le_sup_right
  have hKV : (K : Set G) = (L : Set G) * (KV : Set G) := by
    apply Set.Subset.antisymm
    · intro k hk
      obtain ⟨⟨v, a, n⟩, hprod⟩ := hdec.2 (⟨k, hk⟩ : K)⁻¹
      have hprod' : (v : G) * (a : G) * (n : G) = k⁻¹ :=
        congrArg Subtype.val hprod
      have hinv : (n : G)⁻¹ * (a : G)⁻¹ * (v : G)⁻¹ = k := by
        simpa only [mul_inv_rev, mul_assoc, inv_inv] using congrArg Inv.inv hprod'
      rw [hL_NM, ← hinv]
      exact Set.mul_mem_mul (Set.mul_mem_mul (KN.inv_mem n.property) (KM.inv_mem a.property))
        (KV.inv_mem v.property)
    · rintro k ⟨l, hl, v, hv, rfl⟩
      exact K.mul_mem (hLK hl) hv.1
  constructor
  · rw [← hL_NM]
    change DoubleCoset.doubleCoset g K K = DoubleCoset.doubleCoset g L K
    apply Set.Subset.antisymm _ (fun _ hx => by
      obtain ⟨l, hl, k, hk, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hx
      exact DoubleCoset.mem_doubleCoset.mpr ⟨l, hLK hl, k, hk, rfl⟩)
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hx
    have ha' : a ∈ (L : Set G) * (KV : Set G) := hKV ▸ ha
    obtain ⟨l, hl, v, hv, rfl⟩ := Set.mem_mul.mp ha'
    exact DoubleCoset.mem_doubleCoset.mpr
      ⟨l, hl, (g⁻¹ * v * g) * b, K.mul_mem (mem_conjSubgroup.mp (hVJ hv)) hb, by group⟩
  have levi_eq (v v' : Nbar) (a a' : M) (n n' : N)
      (h : (v : G) * (a : G) * (n : G) = (v' : G) * (a' : G) * (n' : G)) :
      (a : G) = (a' : G) :=
    congrArg (fun t : Nbar × M × N => (t.2.1 : G))
      (hcell (a₁ := (v, a, n)) (a₂ := (v', a', n')) h)
  have hJL : J ⊓ L = J ⊓ H := by
    apply le_antisymm _ (inf_le_inf_left J hHL)
    rintro x ⟨hxJ, hxL⟩
    have hxprod : x ∈ (KM : Set G) * (KN : Set G) := hL_MN ▸ hxL
    obtain ⟨a, ha, n, hn, hax⟩ := Set.mem_mul.mp hxprod
    obtain ⟨⟨v₀, a₀, n₀⟩, h₀⟩ := hdec.2 (⟨g⁻¹ * x * g, mem_conjSubgroup.mp hxJ⟩ : K)
    have h₀' : (v₀ : G) * (a₀ : G) * (n₀ : G) = g⁻¹ * x * g :=
      congrArg Subtype.val h₀
    let v' : Nbar := ⟨g * (v₀ : G) * g⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hMV m.property) _).mp v₀.property.2⟩
    let a' : M := ⟨g * (a₀ : G) * g⁻¹, M.mul_mem (M.mul_mem m.property a₀.property.2)
      (M.inv_mem m.property)⟩
    let n' : N := ⟨g * (n₀ : G) * g⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hMN m.property) _).mp n₀.property.2⟩
    have hcmp : (1 : G) * a * n = (v' : G) * (a' : G) * (n' : G) := by
      rw [one_mul, hax]
      calc
        x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = _ := by rw [← h₀']; dsimp [v', a', n']; group
    have ha' : a = (a' : G) := levi_eq 1 v' ⟨a, ha.2⟩ a' ⟨n, hn.2⟩ n' hcmp
    have haJ : a ∈ J := by
      rw [ha']
      apply mem_conjSubgroup.mpr
      change g⁻¹ * (g * (a₀ : G) * g⁻¹) * g ∈ K
      rw [show g⁻¹ * (g * (a₀ : G) * g⁻¹) * g = a₀ by group]
      exact a₀.property.1
    refine ⟨hxJ, ?_⟩
    rw [← hax]
    exact H.mul_mem ((le_sup_left : J ⊓ KM ≤ H) ⟨haJ, ha⟩) ((le_sup_right : KN ≤ H) hn)
  have hHM : H ⊓ KM = J ⊓ KM := by
    apply le_antisymm _ (le_inf le_sup_left inf_le_right)
    rintro x ⟨hxH, hxM⟩
    have hxprod : x ∈ ((J ⊓ KM : Subgroup G) : Set G) * (KN : Set G) := hH_MN ▸ hxH
    obtain ⟨a, ha, n, hn, hax⟩ := Set.mem_mul.mp hxprod
    have hcmp : (1 : G) * x * 1 = 1 * a * n := by
      simpa only [one_mul, mul_one] using hax.symm
    have heq : x = a := levi_eq 1 1 ⟨x, hxM.2⟩ ⟨a, ha.2.2⟩ 1 ⟨n, hn.2⟩ hcmp
    exact ⟨heq.symm ▸ ha.1, hxM⟩
  have hKIndex : J.relIndex K = J.relIndex L :=
    relIndex_eq_of_coset_cover hLK (by rw [hKV]; exact Set.mul_subset_mul_left hVJ)
  have hLIndex : H.relIndex L = H.relIndex KM :=
    relIndex_eq_of_coset_cover le_sup_left
      (by rw [hL_MN]; exact Set.mul_subset_mul_left (show KN ≤ H from le_sup_right))
  have hHIndex : J.relIndex H = J.relIndex KN :=
    relIndex_eq_of_coset_cover le_sup_right
      (by rw [hH_NM]; exact Set.mul_subset_mul_left (show J ⊓ KM ≤ J from inf_le_left))
  have hMIndex : H.relIndex KM = J.relIndex KM := by
    rw [← Subgroup.inf_relIndex_right H KM, hHM, Subgroup.inf_relIndex_right]
  have hTower := Subgroup.relIndex_inf_mul_relIndex J H L
  rw [inf_eq_left.mpr hHL, ← hJL, Subgroup.inf_relIndex_right, hHIndex, hLIndex,
    hMIndex] at hTower
  change J.relIndex K = (conjSubgroup g KM).relIndex KM * (conjSubgroup g KN).relIndex KN
  rw [hKIndex, ← hTower, mul_comm,
    relIndex_conjSubgroup_inf (M.le_normalizer m.property),
    relIndex_conjSubgroup_inf (hMN m.property)]

/-- The corrected Renard VII.1.2 set, index and Haar volume formulas. -/
theorem iwahoriLeviDoubleCosetVolume : IwahoriLeviDoubleCosetVolumeStatement.{u} := by
  intro G _ _ _ _ K M N Nbar hMN hN m hK hMV hcell hdec hweak
  obtain ⟨hup, hdown⟩ := hweak (m : G) (Set.mem_singleton _)
  have hVJ : K.toSubgroup ⊓ Nbar ≤ conjSubgroup (m : G) K.toSubgroup := by
    intro v hv
    have hv' : (m : G)⁻¹ * v * ((m : G)⁻¹)⁻¹ ∈ K.toSubgroup ⊓ Nbar :=
      hdown ⟨v, hv, rfl⟩
    rw [inv_inv] at hv'
    exact mem_conjSubgroup.mpr hv'.1
  obtain ⟨hset, hindex⟩ := iwahoriDoubleCoset_set_index K.toSubgroup M N Nbar
    hMN hMV m hcell hdec hVJ
  refine ⟨hset, hindex, ?_⟩
  intro _ _ μ _
  have hmod := (contractedIntersection_relIndex K hK N hN ⟨m, hMN m.property⟩ hup).2
  change ((conjSubgroup (m : G) (K.toSubgroup ⊓ N)).relIndex (K.toSubgroup ⊓ N) : ℝ) =
    (((HaarModulus.closedRestrictCharacter N hN M hMN m : ℝ≥0) : ℝ)⁻¹) at hmod
  calc
    _ = (doubleCosetIndex K.toSubgroup m : ℝ≥0∞) * μ (K : Set G) :=
      measure_doubleCoset μ K.toSubgroup K.isOpen.measurableSet m
        (doubleCosetIndex_ne_zero_of_compact_open K hK m)
    _ = _ := by rw [hindex, Nat.cast_mul, ← hmod, ENNReal.ofReal_natCast]

end Langlands.HarishChandraSchwartz
