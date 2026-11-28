import Langlands.Covering.KazhdanPatterson.BruhatSection
import Langlands.Group.GL.UpperUnipotentPowers
import Mathlib.Algebra.Group.Conj

/-! # Compatibility of unipotent splittings with lifted conjugation -/

namespace Langlands.KazhdanPatterson

open Matrix (SpecialLinearGroup)
open Matrix.SpecialLinearGroup (toGL toGL_injective toGLKerEquiv)

universe u v

variable {F : Type u} [Field F] {n : ℕ} {W : Type v} [Group W]
variable {q : W →* SpecialLinearGroup (Fin n) F}

private def fromUpperUnipotent (a : GeneralLinear.upperUnipotent n F) :
    slUpperUnipotent n F := by
  have hd : GeneralLinear.determinant a.val = 1 := by
    apply Units.ext
    change a.val.val.det = 1
    rw [Matrix.det_of_isUpperTriangular a.property.1]
    simp only [show ∀ i, a.val.val i i = 1 from a.property.2, Finset.prod_const_one]
  let d : (GeneralLinear.determinant (n := n) (R := F)).ker := ⟨a.val, hd⟩
  refine ⟨toGLKerEquiv.symm d, ?_⟩
  change toGL (toGLKerEquiv.symm d) ∈ GeneralLinear.upperUnipotent n F
  rw [show toGL (toGLKerEquiv.symm d) = a.val from
    congrArg Subtype.val (toGLKerEquiv.apply_symm_apply d)]
  exact a.property

private theorem toGL_fromUpperUnipotent (a : GeneralLinear.upperUnipotent n F) :
    toGL (fromUpperUnipotent a).val = a.val := by
  unfold fromUpperUnipotent
  exact congrArg Subtype.val (toGLKerEquiv.apply_symm_apply _)

private noncomputable def slUnipotentRoot (e : ℕ) (a : slUpperUnipotent n F) :
    slUpperUnipotent n F :=
  fromUpperUnipotent (GeneralLinear.upperUnipotentPowerRoot e ⟨toGL a.val, a.property⟩)

private theorem slUnipotentRoot_pow (e : ℕ) (he : (e : F) ≠ 0)
    (a : slUpperUnipotent n F) : slUnipotentRoot e a ^ e = a := by
  apply Subtype.ext
  apply toGL_injective
  rw [Subgroup.coe_pow, map_pow, slUnipotentRoot, toGL_fromUpperUnipotent]
  exact congrArg Subtype.val (GeneralLinear.upperUnipotentPowerRoot_pow e he
    ⟨toGL a.val, a.property⟩)

private theorem slUnipotentRoot_mul_eq_mul (e : ℕ) (a b : slUpperUnipotent n F)
    (m : SpecialLinearGroup (Fin n) F) (h : a.val * m = m * b.val) :
    (slUnipotentRoot e a).val * m = m * (slUnipotentRoot e b).val := by
  apply toGL_injective
  simp only [map_mul, slUnipotentRoot, toGL_fromUpperUnipotent]
  exact GeneralLinear.upperUnipotentPowerRoot_mul_eq_mul e ⟨toGL a.val, a.property⟩
    ⟨toGL b.val, b.property⟩ (toGL m) (by simpa only [map_mul] using congrArg toGL h)

private theorem pow_eq_of_map_eq (e : ℕ) (hc : q.ker ≤ Subgroup.center W)
    (he : ∀ z ∈ q.ker, z ^ e = 1) {x y : W} (hxy : q x = q y) : x ^ e = y ^ e := by
  let z := x * y⁻¹
  have hz : z ∈ q.ker := by
    change q (x * y⁻¹) = 1
    rw [map_mul, map_inv, hxy, mul_inv_cancel]
  have hzy : Commute z y := (Subgroup.mem_center_iff.mp (hc hz) y).symm
  have hx : x = z * y := by dsimp [z]; group
  calc
    x ^ e = (z * y) ^ e := congrArg (fun w : W => w ^ e) hx
    _ = y ^ e := by rw [hzy.mul_pow, he z hz, one_mul]

/-- A homomorphic lift of upper-unipotent matrices respects every conjugation
between them that comes from an element of the covering group. -/
theorem unipotentLift_mul_eq_mul (e : ℕ) (hF : (e : F) ≠ 0)
    (hc : q.ker ≤ Subgroup.center W) (he : ∀ z ∈ q.ker, z ^ e = 1)
    (s : slUpperUnipotent n F →* W) (hs : ∀ a, q (s a) = a.val)
    (a b : slUpperUnipotent n F) (w : W) (h : a.val * q w = q w * b.val) :
    s a * w = w * s b := by
  let a₀ := slUnipotentRoot e a
  let b₀ := slUnipotentRoot e b
  have h₀ : a₀.val * q w = q w * b₀.val := slUnipotentRoot_mul_eq_mul e a b (q w) h
  have hq : q (s a₀) = q (w * s b₀ * w⁻¹) := by
    rw [map_mul, map_mul, map_inv, hs, hs, ← h₀, mul_assoc, mul_inv_cancel, mul_one]
  have hpow := pow_eq_of_map_eq e hc he hq
  rw [conj_pow, ← map_pow, ← map_pow, slUnipotentRoot_pow e hF a,
    slUnipotentRoot_pow e hF b] at hpow
  calc
    s a * w = (w * s b * w⁻¹) * w := congrArg (· * w) hpow
    _ = w * s b := by group

/-- A homomorphic lift of the upper-unipotent subgroup is unique. -/
theorem unipotentLift_unique (e : ℕ) (hF : (e : F) ≠ 0)
    (hc : q.ker ≤ Subgroup.center W) (he : ∀ z ∈ q.ker, z ^ e = 1)
    (s t : slUpperUnipotent n F →* W)
    (hs : ∀ a, q (s a) = a.val) (ht : ∀ a, q (t a) = a.val) : s = t := by
  ext a
  let b := slUnipotentRoot e a
  have h := pow_eq_of_map_eq e hc he ((hs b).trans (ht b).symm)
  rw [← map_pow, ← map_pow, slUnipotentRoot_pow e hF a] at h
  exact h

/-- Assemble the Bruhat lifts in an extension whose central kernel has
exponent dividing `e`, assuming `e` is invertible in the field. -/
def BruhatLiftData.ofCentralKernel (e : ℕ) (hF : (e : F) ≠ 0)
    (hc : q.ker ≤ Subgroup.center W) (he : ∀ z ∈ q.ker, z ^ e = 1)
    (s : slUpperUnipotent n F →* W) (hs : ∀ a, q (s a) = a.val)
    (t : {m : SpecialLinearGroup (Fin n) F // IsSpecialLinearMonomial m} → W)
    (ht : ∀ m, q (t m) = m.val) (ht₁ : t ⟨1, isSpecialLinearMonomial_one⟩ = 1) :
    BruhatLiftData q where
  unipotent := s
  monomial := t
  unipotent_projects := hs
  monomial_projects := ht
  monomial_one := ht₁
  overlap a m b h := unipotentLift_mul_eq_mul e hF hc he s hs a b (t m)
    (by rwa [ht])

end Langlands.KazhdanPatterson
