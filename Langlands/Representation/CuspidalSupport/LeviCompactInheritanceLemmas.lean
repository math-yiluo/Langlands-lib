import Langlands.Representation.Induction.NormalLevelNormalizedFixedVectors
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! # Subgroup lemmas for compact inheritance by a Levi -/

noncomputable section

namespace Langlands.CuspidalSupport.CompactInheritance

open Aubert.General BruhatTits.SpecialCompact

universe u

variable {H : Type u} [Group H]

/-- Restrict an Iwahori product when its factors belong to the restricting
subgroup whenever their product does. -/
theorem restrict_iwahori {K L N B M : Subgroup H}
    (h : HasIwahoriIntersectionDecomposition K L N B)
    (hfactors : ∀ (x : ↥(K ⊓ B)) (y : ↥(K ⊓ L)) (z : ↥(K ⊓ N)),
      (x : H) * (y : H) * (z : H) ∈ M →
        (x : H) ∈ M ∧ (y : H) ∈ M ∧ (z : H) ∈ M) :
    HasIwahoriIntersectionDecomposition (K ⊓ M) L (N ⊓ M) (B ⊓ M) := by
  constructor
  · rintro ⟨x, y, z⟩ ⟨x', y', z'⟩ he
    have he' : orderedIntersectionProduct K L N B
        (⟨x, x.property.1.1, x.property.2.1⟩,
          ⟨y, y.property.1.1, y.property.2⟩,
          ⟨z, z.property.1.1, z.property.2.1⟩) =
        orderedIntersectionProduct K L N B
        (⟨x', x'.property.1.1, x'.property.2.1⟩,
          ⟨y', y'.property.1.1, y'.property.2⟩,
          ⟨z', z'.property.1.1, z'.property.2.1⟩) :=
      Subtype.ext (congrArg (fun v : ↥(K ⊓ M) => (v : H)) he)
    have heq := h.injective he'
    have hx : x = x' := Subtype.ext (congrArg (fun t => (t.1 : H)) heq)
    have hy : y = y' := Subtype.ext (congrArg (fun t => (t.2.1 : H)) heq)
    have hz : z = z' := Subtype.ext (congrArg (fun t => (t.2.2 : H)) heq)
    exact Prod.ext hx (Prod.ext hy hz)
  · intro k
    obtain ⟨⟨x, y, z⟩, he⟩ := h.surjective ⟨k, k.property.1⟩
    have hprod : (x : H) * (y : H) * (z : H) = k := congrArg Subtype.val he
    obtain ⟨hx, hy, hz⟩ := hfactors x y z (hprod ▸ k.property.2)
    refine ⟨(⟨x, ⟨x.property.1, hx⟩, x.property.2, hx⟩,
      ⟨y, ⟨y.property.1, hy⟩, y.property.2⟩,
      ⟨z, ⟨z.property.1, hz⟩, z.property.2, hz⟩), Subtype.ext hprod⟩

/-- Nested radical products force the factors of a product in the Levi to
lie in that Levi. -/
theorem factors_mem_of_nested_radicals {P M U B L N C : Subgroup H}
    (hM : M ≤ P) (hU : U ≤ P) (hL : L ≤ M)
    (htrivial : ∀ x : H, x ∈ B → x ∈ P → x = 1)
    (hC : ∀ x ∈ C, ∃ a ∈ B, ∃ b ∈ M, x = a * b)
    (hN : ∀ z ∈ N, ∃ c ∈ M, ∃ d ∈ U, z = c * d)
    {x y z : H} (hx : x ∈ C) (hy : y ∈ L) (hz : z ∈ N)
    (hxyz : x * y * z ∈ M) : x ∈ M ∧ y ∈ M ∧ z ∈ M := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hC x hx
  obtain ⟨c, hc, d, hd, rfl⟩ := hN z hz
  have haP : a ∈ P := by
    have he : a = ((a * b) * y * (c * d)) * (b * y * c * d)⁻¹ := by group
    rw [he]
    exact P.mul_mem (hM hxyz)
      (P.inv_mem (P.mul_mem (P.mul_mem (P.mul_mem (hM hb) (hM (hL hy))) (hM hc))
        (hU hd)))
  have ha1 := htrivial a ha haP
  subst a
  simp only [one_mul] at hxyz ⊢
  refine ⟨hb, hL hy, ?_⟩
  have he : c * d = (b * y)⁻¹ * (b * y * (c * d)) := by group
  rw [he]
  exact M.mul_mem (M.inv_mem (M.mul_mem hb (hL hy))) hxyz

/-- Image in the ambient group of a subgroup intersected with a parabolic. -/
def projectedSubgroup {P M U : Subgroup H}
    (h : IsSemidirectDecomposition P M U) (K₀ : Subgroup H) : Subgroup H :=
  (K₀.comap P.subtype).map (M.subtype.comp h.projection)

theorem projectedSubgroup_le {P M U : Subgroup H}
    (h : IsSemidirectDecomposition P M U) (K₀ : Subgroup H) :
    projectedSubgroup h K₀ ≤ M := by
  rintro _ ⟨p, _, rfl⟩
  exact (h.projection p).property

/-- The projected subgroup contains the level in the Levi and normalizes it
when projection preserves the level. -/
theorem projectedSubgroup_normalizes {P M U : Subgroup H}
    (h : IsSemidirectDecomposition P M U) {K K₀ : Subgroup H}
    (hKK₀ : K ≤ K₀) (hnormal : K₀ ≤ Subgroup.normalizer K)
    (hprojection : ∀ p : P, (p : H) ∈ K → ((h.projection p : M) : H) ∈ K) :
    K ⊓ M ≤ projectedSubgroup h K₀ ∧
      projectedSubgroup h K₀ ≤ Subgroup.normalizer (K ⊓ M : Subgroup H) := by
  have hinc : K ⊓ M ≤ projectedSubgroup h K₀ := by
    intro k hk
    refine ⟨⟨k, h.levi_le hk.2⟩, hKK₀ hk.1, ?_⟩
    change ((h.projection ⟨k, h.levi_le hk.2⟩ : M) : H) = k
    exact congrArg Subtype.val (h.projection_levi ⟨k, hk.2⟩)
  refine ⟨hinc, Subgroup.le_normalizer_iff.mpr ?_⟩
  rintro _ ⟨p, hp, rfl⟩ k hk
  let kP : P := ⟨k, h.levi_le hk.2⟩
  have hconj : ((p * kP * p⁻¹ : P) : H) ∈ K :=
    (Subgroup.le_normalizer_iff.mp hnormal) p hp k hk.1
  have hproj := hprojection (p * kP * p⁻¹) hconj
  have hkproj : h.projection kP = ⟨k, hk.2⟩ := h.projection_levi ⟨k, hk.2⟩
  have hprojval : ((h.projection (p * kP * p⁻¹) : M) : H) =
      ((h.projection p : M) : H) * k * ((h.projection p : M) : H)⁻¹ := by
    rw [map_mul, map_mul, map_inv, hkproj]
    rfl
  refine ⟨hprojval ▸ hproj, ?_⟩
  exact M.mul_mem (M.mul_mem (h.projection p).property hk.2)
    (M.inv_mem (h.projection p).property)

section Topology

variable [TopologicalSpace H]

/-- A compact subgroup has compact projected intersection with a closed
parabolic under a continuous Levi projection. -/
theorem projectedSubgroup_isCompact {P M U : Subgroup H}
    (h : IsSemidirectDecomposition P M U) (hP : IsClosed (P : Set H))
    (hprojection : Continuous h.projection) {K₀ : Subgroup H}
    (hK₀ : IsCompact (K₀ : Set H)) : IsCompact (projectedSubgroup h K₀ : Set H) := by
  have hemb : Topology.IsClosedEmbedding (P.subtype : P → H) :=
    hP.isClosedEmbedding_subtypeVal
  have hcompact : IsCompact ((K₀.comap P.subtype : Subgroup P) : Set P) :=
    hemb.isCompact_preimage hK₀
  exact hcompact.image (continuous_subtype_val.comp hprojection)

end Topology

end Langlands.CuspidalSupport.CompactInheritance
