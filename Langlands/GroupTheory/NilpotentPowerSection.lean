import Mathlib.Algebra.Group.Conj
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Tactic.Group

/-! # Splitting central extensions of uniquely divisible nilpotent groups -/

namespace Langlands

open Subgroup (center mem_center_iff)
open QuotientGroup (mk')

universe u v

variable {G : Type u} {E : Type v} [Group G] [Group E]

private theorem same_power_of_same_image (e : ℕ) (q : E →* G)
    (hc : q.ker ≤ center E) (hk : ∀ z ∈ q.ker, z ^ e = 1)
    {x y : E} (h : q x = q y) : x ^ e = y ^ e := by
  have hker : x / y ∈ q.ker := by simp [h]
  have hcomm : Commute (x / y) y := (mem_center_iff.mp (hc hker) y).symm
  calc
    x ^ e = (x / y * y) ^ e := by rw [div_mul_cancel]
    _ = y ^ e := by rw [hcomm.mul_pow, hk _ hker, one_mul]

private theorem root_mem_center (e : ℕ) (hi : Function.Injective (fun a : G => a ^ e))
    {a : G} (ha : a ^ e ∈ center G) : a ∈ center G := by
  apply mem_center_iff.mpr
  intro g
  have h : g * a * g⁻¹ = a := hi (by
    change (g * a * g⁻¹) ^ e = a ^ e
    rw [conj_pow, mem_center_iff.mp ha g, mul_assoc, mul_inv_cancel, mul_one])
  calc
    g * a = (g * a * g⁻¹) * g := by group
    _ = a * g := congrArg (· * g) h

private theorem quotient_center_power_bijective (e : ℕ)
    (hp : Function.Bijective (fun a : G => a ^ e)) :
    Function.Bijective (fun a : G ⧸ center G => a ^ e) := by
  constructor
  · intro x y h
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (center G) x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (center G) y
    change mk' (center G) a ^ e = mk' (center G) b ^ e at h
    rw [← map_pow, ← map_pow] at h
    obtain ⟨z, hz, hab⟩ := (QuotientGroup.mk'_eq_mk' (center G)).mp h
    obtain ⟨w, hw⟩ := hp.2 z
    change w ^ e = z at hw
    have hwc : w ∈ center G := root_mem_center e hp.1 (by rwa [hw])
    have hcomm : Commute a w := mem_center_iff.mp hwc a
    apply (QuotientGroup.mk'_eq_mk' (center G)).mpr
    refine ⟨w, hwc, hp.1 ?_⟩
    change (a * w) ^ e = b ^ e
    rw [hcomm.mul_pow, hw, hab]
  · intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (center G) x
    obtain ⟨b, hb⟩ := hp.2 a
    exact ⟨mk' (center G) b, (map_pow (mk' (center G)) b e).symm.trans
      (congrArg (mk' (center G)) hb)⟩

private noncomputable def powerLift (e : ℕ) (q : E →* G) (hq : Function.Surjective q)
    (hp : Function.Bijective (fun a : G => a ^ e)) (a : G) : E :=
  (hq (hp.2 a).choose).choose ^ e

private theorem powerLift_projects (e : ℕ) (q : E →* G) (hq : Function.Surjective q)
    (hp : Function.Bijective (fun a : G => a ^ e)) (a : G) :
    q (powerLift e q hq hp a) = a := by
  rw [powerLift, map_pow, (hq (hp.2 a).choose).choose_spec]
  exact (hp.2 a).choose_spec

private theorem powerLift_eq_pow (e : ℕ) (q : E →* G) (hq : Function.Surjective q)
    (hp : Function.Bijective (fun a : G => a ^ e)) (hc : q.ker ≤ center E)
    (hk : ∀ z ∈ q.ker, z ^ e = 1) {a : G} (x : E) (hx : q x ^ e = a) :
    powerLift e q hq hp a = x ^ e := by
  apply same_power_of_same_image e q hc hk
  rw [(hq (hp.2 a).choose).choose_spec]
  exact hp.1 ((hp.2 a).choose_spec.trans hx.symm)

private theorem comap_center_le_center (e : ℕ) (q : E →* G) (hq : Function.Surjective q)
    (hp : Function.Bijective (fun a : G => a ^ e)) (hc : q.ker ≤ center E)
    (hk : ∀ z ∈ q.ker, z ^ e = 1) : (center G).comap q ≤ center E := by
  intro x hx
  change q x ∈ center G at hx
  obtain ⟨a, ha⟩ := hp.2 (q x)
  change a ^ e = q x at ha
  obtain ⟨y, hy⟩ := hq a
  have hya : q y ∈ center G := by
    rw [hy]
    exact root_mem_center e hp.1 (by rwa [ha])
  have hpow : y ^ e ∈ center E := by
    apply mem_center_iff.mpr
    intro g
    have h : q (g * y * g⁻¹) = q y := by
      rw [map_mul, map_mul, map_inv, mem_center_iff.mp hya (q g), mul_assoc,
        mul_inv_cancel, mul_one]
    have hconj := same_power_of_same_image e q hc hk h
    rw [conj_pow] at hconj
    calc
      g * y ^ e = (g * y ^ e * g⁻¹) * g := by group
      _ = y ^ e * g := congrArg (· * g) hconj
  have hker : x / y ^ e ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_div, map_pow, hy, ha, div_self']
  rw [← div_mul_cancel x (y ^ e)]
  exact (center E).mul_mem (hc hker) hpow

private noncomputable def centerPowerLift (e : ℕ) (q : E →* G) (hq : Function.Surjective q)
    (hp : Function.Bijective (fun a : G => a ^ e)) (hc : q.ker ≤ center E)
    (hk : ∀ z ∈ q.ker, z ^ e = 1) : center G →* E where
  toFun a := powerLift e q hq hp a.val
  map_one' := by
    simpa using powerLift_eq_pow e q hq hp hc hk (1 : E) (a := 1) (by simp)
  map_mul' a b := by
    change powerLift e q hq hp (a.val * b.val) =
      powerLift e q hq hp a.val * powerLift e q hq hp b.val
    obtain ⟨a₀, ha₀⟩ := hp.2 a.val
    obtain ⟨b₀, hb₀⟩ := hp.2 b.val
    obtain ⟨x, hx⟩ := hq a₀
    obtain ⟨y, hy⟩ := hq b₀
    have hxa : q x ^ e = a.val := (congrArg (· ^ e) hx).trans ha₀
    have hyb : q y ^ e = b.val := (congrArg (· ^ e) hy).trans hb₀
    have hxc : q x ∈ center G := root_mem_center e hp.1 (hxa ▸ a.property)
    have hcomm : Commute x y :=
      (mem_center_iff.mp (comap_center_le_center e q hq hp hc hk hxc) y).symm
    have hxy : q (x * y) ^ e = a.val * b.val := by
      rw [map_mul, (hcomm.map q).mul_pow, hxa, hyb]
    rw [powerLift_eq_pow e q hq hp hc hk (x * y) hxy,
      powerLift_eq_pow e q hq hp hc hk x hxa, powerLift_eq_pow e q hq hp hc hk y hyb,
      hcomm.mul_pow]

private theorem powerLift_mul [Group.IsNilpotent G] (e : ℕ)
    (q : E →* G) (hq : Function.Surjective q) (hp : Function.Bijective (fun a : G => a ^ e))
    (hc : q.ker ≤ center E) (hk : ∀ z ∈ q.ker, z ^ e = 1) (a b : G) :
    powerLift e q hq hp (a * b) = powerLift e q hq hp a * powerLift e q hq hp b := by
  revert E hp a b
  refine @Group.nilpotent_center_quotient_ind
    (fun (B : Type u) [Group B] [Group.IsNilpotent B] =>
      ∀ {D : Type v} [Group D] (p : D →* B) (hp₁ : Function.Surjective p)
        (hp₂ : Function.Bijective (fun x : B => x ^ e)),
        p.ker ≤ center D → (∀ z ∈ p.ker, z ^ e = 1) → ∀ a b,
          powerLift e p hp₁ hp₂ (a * b) = powerLift e p hp₁ hp₂ a * powerLift e p hp₁ hp₂ b)
    G _ _ ?_ ?_
  · intro G _ _ E _ q hq hp hc hk a b
    have h (x : G) : powerLift e q hq hp x = 1 := by
      rw [powerLift_eq_pow e q hq hp hc hk (1 : E) (Subsingleton.elim _ x), one_pow]
    simp only [h, one_mul]
  · intro G _ _ ih E _ q hq hp hc hk a b
    let z := centerPowerLift e q hq hp hc hk
    let Z := z.range
    have hzq (c : center G) : q (z c) = c.val := powerLift_projects e q hq hp c.val
    have hZ : Z ≤ (center G).comap q := by
      rintro _ ⟨c, rfl⟩
      change q (z c) ∈ center G
      rw [hzq]
      exact c.property
    have hcenter := comap_center_le_center e q hq hp hc hk
    let : Z.Normal := Subgroup.normal_of_le_center (hZ.trans hcenter)
    let p := QuotientGroup.map Z (center G) q hZ
    have hsur : Function.Surjective p :=
      QuotientGroup.map_surjective_of_surjective Z (center G) q
        ((QuotientGroup.mk'_surjective _).comp hq) hZ
    have hkernel {x : E} (hx : mk' Z x ∈ p.ker) : q x ∈ center G :=
      (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hx)
    have hpc : p.ker ≤ center (E ⧸ Z) := by
      intro x hx
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Z x
      apply mem_center_iff.mpr
      intro y
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Z y
      simpa only [map_mul] using congrArg (mk' Z) (mem_center_iff.mp (hcenter (hkernel hx)) y)
    have hpe : ∀ x ∈ p.ker, x ^ e = 1 := by
      intro x hx
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Z x
      let c : center G := ⟨q x, hkernel hx⟩
      have hqz : q x = q (z c) := (hzq c).symm
      have hpow := same_power_of_same_image e q hc hk hqz
      rw [← map_pow, hpow]
      exact (QuotientGroup.eq_one_iff _).mpr (Z.pow_mem ⟨c, rfl⟩ e)
    have hJoint {x y : E} (heq : q x = q y) (hquot : mk' Z x = mk' Z y) : x = y := by
      obtain ⟨_, ⟨c, rfl⟩, hmul⟩ := (QuotientGroup.mk'_eq_mk' Z).mp hquot
      have hc₁ : q x * c.val = q x * 1 := by rw [← hzq, ← map_mul, hmul, ← heq, mul_one]
      have h₁ : c = 1 := Subtype.ext (mul_left_cancel hc₁)
      rw [← hmul, h₁, map_one, mul_one]
    let hp' := quotient_center_power_bijective e hp
    have hcompare (a : G) : mk' Z (powerLift e q hq hp a) =
        powerLift e p hsur hp' (mk' (center G) a) := by
      obtain ⟨b, hb⟩ := hp.2 a
      obtain ⟨x, hx⟩ := hq b
      have ha : q x ^ e = a := (congrArg (· ^ e) hx).trans hb
      rw [powerLift_eq_pow e q hq hp hc hk x ha, map_pow]
      symm
      apply powerLift_eq_pow e p hsur hp' hpc hpe
      change mk' (center G) (q x) ^ e = mk' (center G) a
      rw [← map_pow, ha]
    apply hJoint
    · simp only [map_mul, powerLift_projects]
    · rw [map_mul, hcompare, hcompare, hcompare, map_mul]
      exact ih p hsur hp' hpc hpe (mk' (center G) a) (mk' (center G) b)

/-- The section obtained by taking the `e`-th power of a lift of the unique `e`-th root.
The base is nilpotent, the projection is surjective and the central kernel is killed by `e`. -/
noncomputable def nilpotentPowerSection [Group.IsNilpotent G] (e : ℕ)
    (q : E →* G) (hq : Function.Surjective q) (hp : Function.Bijective (fun a : G => a ^ e))
    (hc : q.ker ≤ center E) (hk : ∀ z ∈ q.ker, z ^ e = 1) : G →* E where
  toFun := powerLift e q hq hp
  map_one' := by
    simpa using powerLift_eq_pow e q hq hp hc hk (1 : E) (a := 1) (by simp)
  map_mul' := powerLift_mul e q hq hp hc hk

theorem nilpotentPowerSection_projects [Group.IsNilpotent G] (e : ℕ)
    (q : E →* G) (hq : Function.Surjective q) (hp : Function.Bijective (fun a : G => a ^ e))
    (hc : q.ker ≤ center E) (hk : ∀ z ∈ q.ker, z ^ e = 1) (a : G) :
    q (nilpotentPowerSection e q hq hp hc hk a) = a :=
  powerLift_projects e q hq hp a

theorem nilpotentPowerSection_apply_pow [Group.IsNilpotent G] (e : ℕ)
    (q : E →* G) (hq : Function.Surjective q) (hp : Function.Bijective (fun a : G => a ^ e))
    (hc : q.ker ≤ center E) (hk : ∀ z ∈ q.ker, z ^ e = 1) (x : E) :
    nilpotentPowerSection e q hq hp hc hk (q x ^ e) = x ^ e :=
  powerLift_eq_pow e q hq hp hc hk x rfl

theorem nilpotentPowerSection_unique [Group.IsNilpotent G] (e : ℕ)
    (q : E →* G) (hq : Function.Surjective q) (hp : Function.Bijective (fun a : G => a ^ e))
    (hc : q.ker ≤ center E) (hk : ∀ z ∈ q.ker, z ^ e = 1)
    (s : G →* E) (hs : ∀ a, q (s a) = a) : s = nilpotentPowerSection e q hq hp hc hk := by
  ext a
  obtain ⟨b, rfl⟩ := hp.2 a
  rw [map_pow, ← nilpotentPowerSection_apply_pow e q hq hp hc hk (s b), hs]

end Langlands
