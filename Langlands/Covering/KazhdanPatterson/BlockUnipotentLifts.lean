import Langlands.Covering.KazhdanPatterson.UnipotentLifts
import Langlands.Group.GL.TriangularParabolic
import Langlands.Representation.Geometric.WeylMinimalRepresentativeProof

/-! # Canonical splittings of standard block unipotent radicals -/

namespace Langlands.GeneralLinear.BlockShape

universe u

variable {r : ℕ} (B : BlockShape r) {F : Type u} [Field F]

/-- The unipotent radical of a standard block parabolic is upper unipotent. -/
theorem unipotentSubgroup_le_upperUnipotent :
    B.unipotentSubgroup F ≤ upperUnipotent r F := by
  intro g hg
  obtain ⟨hp, hd⟩ := (B.mem_unipotentSubgroup_iff F g).mp hg
  constructor
  · intro i j hji
    obtain ⟨⟨s, a⟩, rfl⟩ := B.indexEquiv.surjective i
    obtain ⟨⟨t, b⟩, rfl⟩ := B.indexEquiv.surjective j
    change B.index t b < B.index s a at hji
    rcases lt_trichotomy t s with hts | heq | hst
    · exact (B.mem_parabolic_iff F g).mp hp s t a b hts
    · subst t
      have hba : b < a := (Geometric.index_strictMono B s).lt_iff_lt.mp hji
      change g (B.index s a) (B.index s b) = 0
      simpa [hba.ne.symm] using hd s a b
    · exact ((B.index_lt_index_of_block_lt hst a b).not_gt hji).elim
  · intro i
    obtain ⟨⟨s, a⟩, rfl⟩ := B.indexEquiv.surjective i
    change g (B.index s a) (B.index s a) = 1
    simpa using hd s a a

private theorem leviProjection_mem_upperUnipotent (g : B.parabolic F)
    (hg : g.val ∈ upperUnipotent r F) (i : Fin B.length) :
    B.leviProjection F g i ∈ upperUnipotent (B.size i) F := by
  constructor
  · intro a b hba
    rw [B.leviProjection_apply]
    exact hg.1 (Geometric.index_strictMono B i hba)
  · intro a
    rw [B.leviProjection_apply]
    exact hg.2 (B.index i a)

/-- The upper-unipotent power root of an element of a standard block radical
belongs to that radical. -/
theorem upperUnipotentPowerRoot_mem_unipotentSubgroup (e : ℕ) (hF : (e : F) ≠ 0)
    (g : B.unipotentSubgroup F) :
    (upperUnipotentPowerRoot e ⟨g.val, B.unipotentSubgroup_le_upperUnipotent g.property⟩).val ∈
      B.unipotentSubgroup F := by
  let u : upperUnipotent r F := ⟨g.val, B.unipotentSubgroup_le_upperUnipotent g.property⟩
  let v := upperUnipotentPowerRoot e u
  have hv : v.val ^ e = g.val :=
    congrArg Subtype.val (upperUnipotentPowerRoot_pow e hF u)
  let p : B.parabolic F := ⟨v.val, B.mem_parabolic_of_isUpperTriangular v.val v.property.1⟩
  have hp : p ^ e ∈ B.unipotentRadical F := by
    apply (B.mem_unipotentRadical_iff F (p ^ e)).mpr
    intro i a b
    change (v.val ^ e) (B.index i a) (B.index i b) = _
    rw [hv]
    exact ((B.mem_unipotentSubgroup_iff F g.val).mp g.property).2 i a b
  have hpow : (B.leviProjection F p) ^ e = 1 := by
    rw [← map_pow]
    exact hp
  have hlevi : B.leviProjection F p = 1 := by
    funext i
    let d : upperUnipotent (B.size i) F :=
      ⟨B.leviProjection F p i, B.leviProjection_mem_upperUnipotent p v.property i⟩
    have hd : d ^ e = 1 := Subtype.ext (congrFun hpow i)
    exact congrArg Subtype.val
      (upperUnipotent_pow_injective e hF (hd.trans (one_pow e).symm))
  exact ⟨p, hlevi, rfl⟩

/-- The power bijection of the full upper-unipotent group restricts to the
unipotent radical of a standard block parabolic. -/
noncomputable def unipotentSubgroupPowerEquiv (e : ℕ) (hF : (e : F) ≠ 0) :
    B.unipotentSubgroup F ≃ B.unipotentSubgroup F where
  toFun a := a ^ e
  invFun a := ⟨upperUnipotentPowerRoot e
    ⟨a.val, B.unipotentSubgroup_le_upperUnipotent a.property⟩,
    B.upperUnipotentPowerRoot_mem_unipotentSubgroup e hF a⟩
  left_inv a := by
    apply Subtype.ext
    exact congrArg (fun x : upperUnipotent r F => x.val)
      ((upperUnipotentPowerEquiv e hF).symm_apply_apply
        ⟨a.val, B.unipotentSubgroup_le_upperUnipotent a.property⟩)
  right_inv a := by
    apply Subtype.ext
    exact congrArg (fun x : upperUnipotent r F => x.val)
      (upperUnipotentPowerRoot_pow e hF
        ⟨a.val, B.unipotentSubgroup_le_upperUnipotent a.property⟩)

end Langlands.GeneralLinear.BlockShape

namespace Langlands.KazhdanPatterson

universe u v

variable {F : Type u} [Field F] {r : ℕ} {W : Type v} [Group W]

/-- The canonical splitting over the unipotent radical of a standard block parabolic. -/
@[instance_reducible]
noncomputable def blockUnipotentSplitting (B : GeneralLinear.BlockShape r)
    (e : ℕ) (hF : (e : F) ≠ 0)
    (q : W →* GeneralLinear r F) (hq : Function.Surjective q)
    (hc : q.ker ≤ Subgroup.center W) (hk : ∀ z ∈ q.ker, z ^ e = 1) :
    Unique {s : B.unipotentSubgroup F →* W // ∀ a, q (s a) = a.val} := by
  let : Group.IsNilpotent (GeneralLinear.upperUnipotent r F) :=
    GeneralLinear.upperUnipotent_isNilpotent r F
  let : Group.IsNilpotent (B.unipotentSubgroup F) :=
    (Group.isNilpotent_congr
      (Subgroup.subgroupOfEquivOfLe (B.unipotentSubgroup_le_upperUnipotent (F := F)))).mp
      inferInstance
  exact subgroupPowerSplitting _ e q hq (B.unipotentSubgroupPowerEquiv e hF).bijective hc hk

end Langlands.KazhdanPatterson
