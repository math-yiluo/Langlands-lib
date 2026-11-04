import Langlands.BruhatTits.SpecialCompact.SmallSubgroupPredicates
import Langlands.BruhatTits.SpecialCompact.ContractionPredicates
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.DoubleCosetMeasure

/-! # Upper relative indices from one ordered decomposition -/

noncomputable section

universe u

namespace Langlands.HarishChandraSchwartz

open BruhatTits.SpecialCompact

variable {G : Type u} [Group G]

/-- If the Levi and opposite intersections lie in `J`, every left `J`-coset
in `K` has a representative in the unipotent intersection. -/
theorem relIndex_eq_unipotent_of_iwahori (K J M U V : Subgroup G)
    (hdec : HasIwahoriIntersectionDecomposition K M U V)
    (hM : K ⊓ M ≤ J) (hV : K ⊓ V ≤ J) :
    J.relIndex K = J.relIndex (K ⊓ U) := by
  let e := Subgroup.quotientSubgroupOfEmbeddingOfLE J (show K ⊓ U ≤ K from inf_le_left)
  have he : Function.Surjective e := by
    intro q
    refine Quotient.inductionOn q ?_
    intro k
    obtain ⟨⟨v, m, u⟩, hprod⟩ := hdec.2 k⁻¹
    refine ⟨QuotientGroup.mk u⁻¹, ?_⟩
    change QuotientGroup.mk (Subgroup.inclusion inf_le_left u⁻¹) = QuotientGroup.mk k
    apply QuotientGroup.eq.mpr
    change ((u : G)⁻¹)⁻¹ * (k : G) ∈ J
    rw [inv_inv]
    have hk : (k : G) = (u : G)⁻¹ * (m : G)⁻¹ * (v : G)⁻¹ := by
      have hp : (v : G) * (m : G) * (u : G) = (k : G)⁻¹ := congrArg Subtype.val hprod
      calc (k : G) = ((v : G) * (m : G) * (u : G))⁻¹ := by rw [hp, inv_inv]
           _ = _ := by group
    rw [hk]
    simpa only [mul_assoc, mul_inv_cancel_left] using
      J.mul_mem (J.inv_mem (hM m.property)) (J.inv_mem (hV v.property))
  exact Nat.card_congr (Equiv.ofBijective e ⟨e.injective, he⟩).symm

/-- A weak contraction bounds the double-coset index using only its contracting
unipotent factor. No decomposition of the intersection subgroup is needed. -/
theorem doubleCosetIndex_le_unipotent_contraction (K M U V : Subgroup G) (g : G)
    (hdec : HasIwahoriIntersectionDecomposition K M U V)
    (hM : ambientConjugate g ((K ⊓ M : Subgroup G) : Set G) = K ⊓ M)
    (hV : ambientConjugate g⁻¹ ((K ⊓ V : Subgroup G) : Set G) ⊆ K ⊓ V)
    (hfin : (conjSubgroup g (K ⊓ U)).relIndex (K ⊓ U) ≠ 0) :
    doubleCosetIndex K g ≠ 0 ∧
      doubleCosetIndex K g ≤ (conjSubgroup g (K ⊓ U)).relIndex (K ⊓ U) := by
  have hM' : K ⊓ M ≤ conjSubgroup g K := by
    intro m hm
    have hm' : m ∈ ambientConjugate g ((K ⊓ M : Subgroup G) : Set G) := by
      rw [hM]
      exact hm
    obtain ⟨x, hx, rfl⟩ := hm'
    rw [mem_conjSubgroup]
    simpa [mul_assoc] using hx.1
  have hV' : K ⊓ V ≤ conjSubgroup g K := by
    intro v hv
    rw [mem_conjSubgroup]
    have hv' := hV ⟨v, hv, rfl⟩
    simpa [ambientConjugate, mul_assoc] using hv'.1
  have heq := relIndex_eq_unipotent_of_iwahori K (conjSubgroup g K) M U V hdec hM' hV'
  unfold doubleCosetIndex
  rw [heq]
  have hle : conjSubgroup g (K ⊓ U) ≤ conjSubgroup g K :=
    conjSubgroup_mono g inf_le_left
  exact ⟨ne_zero_of_dvd_ne_zero hfin (Subgroup.relIndex_dvd_of_le_left (K ⊓ U) hle),
    Subgroup.relIndex_le_of_le_left hle hfin⟩

end Langlands.HarishChandraSchwartz
