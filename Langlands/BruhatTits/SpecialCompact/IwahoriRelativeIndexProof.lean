import Langlands.BruhatTits.SpecialCompact.IwahoriRelativeIndexStatement
import Langlands.Group.FactorizationIndexProof

/-! # Proof of the relative Iwahori index product -/

noncomputable section

universe u

namespace Langlands.BruhatTits.SpecialCompact

variable {G : Type u} [Group G]

private theorem complement_lift
    {A B J K : Subgroup G} (hJK : J ≤ K)
    (h : (A.subgroupOf J).IsComplement' (B.subgroupOf J)) :
    ((A.subgroupOf K).subgroupOf (J.subgroupOf K)).IsComplement'
      ((B.subgroupOf K).subgroupOf (J.subgroupOf K)) := by
  constructor
  · intro x y hxy
    have heq :
        (⟨⟨⟨x.1.1.1.1, x.1.1.property⟩, x.1.property⟩,
          ⟨⟨x.2.1.1.1, x.2.1.property⟩, x.2.property⟩⟩ :
          (A.subgroupOf J) × (B.subgroupOf J)) =
        ⟨⟨⟨y.1.1.1.1, y.1.1.property⟩, y.1.property⟩,
          ⟨⟨y.2.1.1.1, y.2.1.property⟩, y.2.property⟩⟩ := by
      apply h.1
      exact Subtype.ext (congrArg (fun z : J.subgroupOf K => ((z : K) : G)) hxy)
    apply Prod.ext <;> apply Subtype.ext <;> apply Subtype.ext <;> apply Subtype.ext
    · exact congrArg (fun z : (A.subgroupOf J) × (B.subgroupOf J) =>
        ((z.1 : J) : G)) heq
    · exact congrArg (fun z : (A.subgroupOf J) × (B.subgroupOf J) =>
        ((z.2 : J) : G)) heq
  · intro x
    obtain ⟨⟨a, b⟩, hab⟩ := h.2 ⟨((x : K) : G), x.property⟩
    refine ⟨⟨⟨⟨⟨(a : J), hJK (a : J).property⟩, (a : J).property⟩, a.property⟩,
      ⟨⟨⟨(b : J), hJK (b : J).property⟩, (b : J).property⟩, b.property⟩⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : J => (z : G)) hab

private theorem relIndex_two
    {A B J K : Subgroup G} (hJK : J ≤ K) [(J.subgroupOf K).Normal]
    (hK : (A.subgroupOf K).IsComplement' (B.subgroupOf K))
    (hJ : (A.subgroupOf J).IsComplement' (B.subgroupOf J)) :
    J.relIndex K = J.relIndex (K ⊓ A) * J.relIndex (K ⊓ B) := by
  have h := Langlands.Group.factorizationIndex K
    (A.subgroupOf K) (B.subgroupOf K) (J.subgroupOf K) hK (complement_lift hJK hJ)
  change J.relIndex K =
    (J.comap K.subtype).relIndex (A.subgroupOf K) *
      (J.comap K.subtype).relIndex (B.subgroupOf K) at h
  simpa only [Subgroup.relIndex_comap, Subgroup.subgroupOf_map_subtype, inf_comm] using h

private theorem iwahori_complement
    {X M U V P : Subgroup G}
    (hMP : M ≤ P) (hUP : U ≤ P) (hVP : Disjoint V P)
    (hX : HasIwahoriIntersectionDecomposition X M U V) :
    (V.subgroupOf X).IsComplement' (P.subgroupOf X) := by
  have hd : Disjoint (V.subgroupOf X) (P.subgroupOf X) := by
    rw [disjoint_iff_inf_le]
    intro x hx
    apply Subtype.ext
    exact (disjoint_iff_inf_le.mp hVP ⟨hx.1, hx.2⟩ : (x : G) = 1)
  refine ⟨Subgroup.mul_injective_of_disjoint hd, ?_⟩
  intro x
  obtain ⟨⟨v, m, u⟩, hvmu⟩ := hX.2 x
  refine ⟨⟨⟨⟨v, v.property.1⟩, v.property.2⟩,
    ⟨⟨(m : G) * (u : G), X.mul_mem m.property.1 u.property.1⟩,
      P.mul_mem (hMP m.property.2) (hUP u.property.2)⟩⟩, ?_⟩
  apply Subtype.ext
  exact (mul_assoc _ _ _).symm.trans (congrArg (fun z : X => (z : G)) hvmu)

private theorem iwahori_parabolic_complement
    {X M U V P : Subgroup G}
    (hMP : M ≤ P) (hUP : U ≤ P) (hVP : Disjoint V P)
    (hX : HasIwahoriIntersectionDecomposition X M U V) :
    (M.subgroupOf (X ⊓ P)).IsComplement' (U.subgroupOf (X ⊓ P)) := by
  constructor
  · intro x y hxy
    let f : (M.subgroupOf (X ⊓ P)) × (U.subgroupOf (X ⊓ P)) →
        ↥(X ⊓ V) × ↥(X ⊓ M) × ↥(X ⊓ U) :=
      fun z => ⟨1, ⟨z.1, z.1.1.property.1, z.1.property⟩,
        ⟨z.2, z.2.1.property.1, z.2.property⟩⟩
    have hf : f x = f y := by
      apply hX.1
      apply Subtype.ext
      simpa only [orderedIntersectionProduct, f, Subgroup.coe_one, Subgroup.coe_mul,
        one_mul] using
        congrArg (fun z : ↥(X ⊓ P) => (z : G)) hxy
    apply Prod.ext <;> apply Subtype.ext <;> apply Subtype.ext
    · exact congrArg (fun z : ↥(X ⊓ V) × ↥(X ⊓ M) × ↥(X ⊓ U) => (z.2.1 : G)) hf
    · exact congrArg (fun z : ↥(X ⊓ V) × ↥(X ⊓ M) × ↥(X ⊓ U) => (z.2.2 : G)) hf
  · intro x
    obtain ⟨⟨v, m, u⟩, hvmu⟩ := hX.2 ⟨x, x.property.1⟩
    have heq : (v : G) * (m : G) * (u : G) = x :=
      congrArg (fun z : X => (z : G)) hvmu
    have hvP : (v : G) ∈ P := by
      have heq' : (v : G) = (x : G) * ((m : G) * (u : G))⁻¹ := by
        apply eq_mul_inv_iff_mul_eq.mpr
        simpa only [mul_assoc] using heq
      rw [heq']
      exact P.mul_mem x.property.2
        (P.inv_mem (P.mul_mem (hMP m.property.2) (hUP u.property.2)))
    have hv1 : (v : G) = 1 := disjoint_iff_inf_le.mp hVP ⟨v.property.2, hvP⟩
    refine ⟨⟨⟨⟨m, m.property.1, hMP m.property.2⟩, m.property.2⟩,
      ⟨⟨u, u.property.1, hUP u.property.2⟩, u.property.2⟩⟩, ?_⟩
    apply Subtype.ext
    change (m : G) * (u : G) = (x : G)
    simpa only [hv1, one_mul] using heq

private theorem relIndex_inf_of_le {J P L : Subgroup G} (hLP : L ≤ P) :
    (J ⊓ P).relIndex L = J.relIndex L := by
  apply congrArg Subgroup.index
  exact Subgroup.ext fun x => and_iff_left (hLP x.property)

private theorem normal_iwahori_index
    {K H M U V P : Subgroup G} (hHK : H ≤ K) [(H.subgroupOf K).Normal]
    (hMP : M ≤ P) (hUP : U ≤ P) (hVP : Disjoint V P)
    (hK : HasIwahoriIntersectionDecomposition K M U V)
    (hH : HasIwahoriIntersectionDecomposition H M U V) :
    H.relIndex K =
      H.relIndex (K ⊓ V) * H.relIndex (K ⊓ M) * H.relIndex (K ⊓ U) := by
  have h₁ := relIndex_two hHK (iwahori_complement hMP hUP hVP hK)
    (iwahori_complement hMP hUP hVP hH)
  have : ((H ⊓ P).subgroupOf (K ⊓ P)).Normal :=
    Subgroup.inf_subgroupOf_inf_normal_of_left P
  have h₂ := relIndex_two (inf_le_inf_right P hHK)
    (iwahori_parabolic_complement hMP hUP hVP hK)
    (iwahori_parabolic_complement hMP hUP hVP hH)
  have hPM : (K ⊓ P) ⊓ M = K ⊓ M := by
    ext x
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hMP h.2⟩, h.2⟩⟩
  have hPU : (K ⊓ P) ⊓ U = K ⊓ U := by
    ext x
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hUP h.2⟩, h.2⟩⟩
  rw [hPM, hPU, relIndex_inf_of_le (inf_le_right : K ⊓ P ≤ P),
    relIndex_inf_of_le (inf_le_right.trans hMP : K ⊓ M ≤ P),
    relIndex_inf_of_le (inf_le_right.trans hUP : K ⊓ U ≤ P)] at h₂
  rw [h₁, h₂, mul_assoc]

/-- The exact relative Iwahori index statement, at every universe. -/
theorem iwahoriRelativeIndex : IwahoriRelativeIndexStatement.{u} := by
  intro G _ K J H M U V P hHJ hJK hnormal hfinite hMP hUP hVP hK hJ hH
  have : (H.subgroupOf K).Normal := hnormal
  have : (H.subgroupOf J).Normal :=
    hnormal.comap (Subgroup.inclusion hJK)
  have hKindex := normal_iwahori_index (hHJ.trans hJK) hMP hUP hVP hK hH
  have hJindex := normal_iwahori_index hHJ hMP hUP hVP hJ hH
  have htower (S : Subgroup G) :
      H.relIndex (J ⊓ S) * J.relIndex (K ⊓ S) = H.relIndex (K ⊓ S) := by
    simpa only [← inf_assoc, inf_eq_left.mpr hJK, inf_eq_left.mpr hHJ] using
      Subgroup.relIndex_inf_mul_relIndex H J (K ⊓ S)
  have hproduct : H.relIndex K = H.relIndex J *
      (J.relIndex (K ⊓ V) * J.relIndex (K ⊓ M) * J.relIndex (K ⊓ U)) := by
    rw [hKindex, ← htower V, ← htower M, ← htower U, hJindex]
    ac_rfl
  have hfiniteJ : H.relIndex J ≠ 0 :=
    fun hzero => hfinite (Subgroup.relIndex_eq_zero_of_le_right hJK hzero)
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hfiniteJ)
  exact (Subgroup.relIndex_mul_relIndex H J K hHJ hJK).trans hproduct

end Langlands.BruhatTits.SpecialCompact
