import Langlands.Covering.KazhdanPatterson.BruhatOverlap
import Langlands.Group.GL.UpperUnipotentNilpotent
import Langlands.GroupTheory.NilpotentPowerSection

/-! # Canonical unipotent splittings for GL and SL -/

namespace Langlands.KazhdanPatterson

open Matrix (SpecialLinearGroup)
open Matrix.SpecialLinearGroup (toGL toGL_injective toGLKerEquiv)

universe u v

section Subgroup

variable {G : Type u} {W : Type v} [Group G] [Group W]

/-- The unique homomorphic lift of a nilpotent subgroup with bijective `e`-th powers
through a surjection with central kernel killed by `e`. -/
@[instance_reducible]
noncomputable def subgroupPowerSplitting (U : Subgroup G) [Group.IsNilpotent U] (e : ℕ)
    (q : W →* G) (hq : Function.Surjective q)
    (hp : Function.Bijective (fun a : U => a ^ e))
    (hc : q.ker ≤ Subgroup.center W) (hk : ∀ z ∈ q.ker, z ^ e = 1) :
    Unique {s : U →* W // ∀ a, q (s a) = a.val} := by
  let p := q.subgroupComap U
  have hsur : Function.Surjective p := q.subgroupComap_surjective U hq
  have hker {x : U.comap q} (hx : x ∈ p.ker) : x.val ∈ q.ker :=
    congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  have hcentral : p.ker ≤ Subgroup.center (U.comap q) := by
    intro x hx
    apply Subgroup.mem_center_iff.mpr
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hc (hker hx)) y.val)
  have hpower : ∀ z ∈ p.ker, z ^ e = 1 :=
    fun z hz => Subtype.ext (hk z.val (hker hz))
  let lift := nilpotentPowerSection e p hsur hp hcentral hpower
  refine { default := ⟨(U.comap q).subtype.comp lift, ?_⟩, uniq := ?_ }
  · intro a
    exact congrArg Subtype.val (nilpotentPowerSection_projects e p hsur hp hcentral hpower a)
  · intro s
    let t := s.val.codRestrict (U.comap q) (fun a => by
      change q (s.val a) ∈ U
      rw [s.property a]
      exact a.property)
    have ht : ∀ a, p (t a) = a := fun a => Subtype.ext (s.property a)
    have heq := nilpotentPowerSection_unique e p hsur hp hcentral hpower t ht
    exact Subtype.ext (congrArg ((U.comap q).subtype.comp ·) heq)

end Subgroup

variable {F : Type u} [Field F] {r : ℕ} {W : Type v} [Group W]

/-- The canonical splitting over the upper-unipotent subgroup of `GL`. -/
@[instance_reducible]
noncomputable def glUpperUnipotentSplitting (e : ℕ) (hF : (e : F) ≠ 0)
    (q : W →* GeneralLinear r F) (hq : Function.Surjective q)
    (hc : q.ker ≤ Subgroup.center W) (hk : ∀ z ∈ q.ker, z ^ e = 1) :
    Unique {s : GeneralLinear.upperUnipotent r F →* W // ∀ a, q (s a) = a.val} :=
  let : Group.IsNilpotent (GeneralLinear.upperUnipotent r F) :=
    GeneralLinear.upperUnipotent_isNilpotent r F
  subgroupPowerSplitting _ e q hq (GeneralLinear.upperUnipotentPowerEquiv e hF).bijective hc hk

/-- The upper-unipotent subgroups of `SL` and `GL` have the same matrices. -/
noncomputable def slUpperUnipotentEquiv : slUpperUnipotent r F ≃* GeneralLinear.upperUnipotent r F :=
  MulEquiv.ofBijective (toGL.subgroupComap (GeneralLinear.upperUnipotent r F)) ⟨
    toGL.subgroupComap_injective _ toGL_injective, fun a => by
      have hd : GeneralLinear.determinant a.val = 1 := by
        apply Units.ext
        change a.val.val.det = 1
        rw [Matrix.det_of_isUpperTriangular a.property.1]
        simp only [show ∀ i, a.val.val i i = 1 from a.property.2, Finset.prod_const_one]
      let d : (GeneralLinear.determinant (n := r) (R := F)).ker := ⟨a.val, hd⟩
      have h : toGL (toGLKerEquiv.symm d) = a.val :=
        congrArg Subtype.val (toGLKerEquiv.apply_symm_apply d)
      refine ⟨⟨toGLKerEquiv.symm d, ?_⟩, Subtype.ext h⟩
      change toGL (toGLKerEquiv.symm d) ∈ GeneralLinear.upperUnipotent r F
      rw [h]
      exact a.property⟩

/-- The canonical splitting over the upper-unipotent subgroup of `SL`. -/
@[instance_reducible]
noncomputable def slUpperUnipotentSplitting (e : ℕ) (hF : (e : F) ≠ 0)
    (q : W →* SpecialLinearGroup (Fin r) F) (hq : Function.Surjective q)
    (hc : q.ker ≤ Subgroup.center W) (hk : ∀ z ∈ q.ker, z ^ e = 1) :
    Unique {s : slUpperUnipotent r F →* W // ∀ a, q (s a) = a.val} := by
  let f : slUpperUnipotent r F ≃* GeneralLinear.upperUnipotent r F := slUpperUnipotentEquiv
  let : Group.IsNilpotent (slUpperUnipotent r F) :=
    (Group.isNilpotent_congr f).mpr (GeneralLinear.upperUnipotent_isNilpotent r F)
  have hp : Function.Bijective (fun a : slUpperUnipotent r F => a ^ e) := by
    have h := f.symm.bijective.comp
      ((GeneralLinear.upperUnipotentPowerEquiv e hF).bijective.comp f.bijective)
    convert h using 1
    funext a
    change a ^ e = f.symm (f a ^ e)
    rw [← map_pow, MulEquiv.symm_apply_apply]
  exact subgroupPowerSplitting _ e q hq hp hc hk

/-- The canonical unipotent splitting supplies the unipotent part of the Bruhat lifts. -/
noncomputable def BruhatLiftData.ofSurjectiveCentralKernel
    {q : W →* SpecialLinearGroup (Fin r) F} (hq : Function.Surjective q)
    (e : ℕ) (hF : (e : F) ≠ 0)
    (hc : q.ker ≤ Subgroup.center W) (hk : ∀ z ∈ q.ker, z ^ e = 1)
    (t : {m : SpecialLinearGroup (Fin r) F // IsSpecialLinearMonomial m} → W)
    (ht : ∀ m, q (t m) = m.val) (ht₁ : t ⟨1, isSpecialLinearMonomial_one⟩ = 1) :
    BruhatLiftData q :=
  let s := (slUpperUnipotentSplitting e hF q hq hc hk).default
  BruhatLiftData.ofCentralKernel e hF hc hk s.val s.property t ht ht₁

end Langlands.KazhdanPatterson
