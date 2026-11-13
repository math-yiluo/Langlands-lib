import Langlands.Cohomology.DivisibleSystem.ProPInvariants
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Pro-p normal subgroups and p-group quotients -/

noncomputable section

universe u v

namespace Langlands.Cohomology

variable {G : Type u} [Group G] [TopologicalSpace G]
  {Q : Type v} [Group Q] [TopologicalSpace Q]

/-- Pull back an open normal subgroup along a continuous homomorphism. -/
def openNormalComap (f : G →* Q) (hf : Continuous f)
    (N : OpenNormalSubgroup Q) : OpenNormalSubgroup G where
  toOpenSubgroup := N.toOpenSubgroup.comap f hf
  isNormal' := N.isNormal'.comap f

@[simp]
theorem openNormalComap_toSubgroup (f : G →* Q) (hf : Continuous f)
    (N : OpenNormalSubgroup Q) :
    (openNormalComap f hf N).toSubgroup = N.toSubgroup.comap f := rfl

/-- If a normal subgroup is pro-p and its abstract quotient is a p-group,
every open normal quotient of the whole group is a p-group. -/
theorem isPGroup_openNormalQuotient_of_extension {p : ℕ} {K : Subgroup G}
    [K.Normal] (hK : IsProPSubgroup p K) (hQ : IsPGroup p (G ⧸ K))
    (N : OpenNormalSubgroup G) : IsPGroup p (G ⧸ N.toSubgroup) := by
  intro z
  refine Quotient.inductionOn' z ?_
  intro x
  obtain ⟨m, hm⟩ := hQ (QuotientGroup.mk x)
  have hx : x ^ p ^ m ∈ K := (QuotientGroup.eq_one_iff _).mp (by
    simpa only [QuotientGroup.mk_pow] using hm)
  let y : K := ⟨x ^ p ^ m, hx⟩
  let M := openNormalComap K.subtype continuous_subtype_val N
  obtain ⟨n, hn⟩ := hK.isPGroup M (QuotientGroup.mk y)
  refine ⟨m + n, ?_⟩
  change (QuotientGroup.mk' N.toSubgroup) x ^ p ^ (m + n) = 1
  rw [← map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  have hy : y ^ p ^ n ∈ M.toSubgroup := (QuotientGroup.eq_one_iff _).mp (by
    simpa only [QuotientGroup.mk_pow] using hn)
  change (x ^ p ^ m) ^ p ^ n ∈ N.toSubgroup at hy
  simpa only [pow_add, pow_mul] using hy

/-- A compact totally disconnected subgroup is pro-p if it has a normal
pro-p subgroup with p-group quotient. -/
theorem IsProPSubgroup.of_isPGroup_quotient {p : ℕ} {H : Subgroup G}
    [CompactSpace H] [TotallyDisconnectedSpace H]
    (K : Subgroup H) [K.Normal] (hK : IsProPSubgroup p K)
    (hQ : IsPGroup p (H ⧸ K)) : IsProPSubgroup p H where
  prime := hK.prime
  compactSpace := inferInstance
  totallyDisconnectedSpace := inferInstance
  isPGroup := isPGroup_openNormalQuotient_of_extension hK hQ

end Langlands.Cohomology
