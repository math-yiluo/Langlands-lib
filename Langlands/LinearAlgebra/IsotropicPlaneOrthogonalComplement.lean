import Langlands.LinearAlgebra.SymmetricHyperbolicPair

/-! # An isotropic plane leaves an isotropic vector after one hyperbolic plane is removed -/

noncomputable section

universe u v

namespace Langlands.SymmetricBilinear.HyperbolicPair

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {B : LinearMap.BilinForm K V} (P : HyperbolicPair B)

/-- An arbitrary hyperbolic plane has isotropic orthogonal complement if the
  ambient symmetric form contains a totally isotropic plane. -/
theorem exists_isotropic_in_complement_of_plane (hS : B.IsSymm) {x y : V}
    (hli : LinearIndependent K ![x, y]) (hx : B x x = 0) (hxy : B x y = 0) (hy : B y y = 0) :
    ∃ z : P.orthogonalComplement, z ≠ 0 ∧ B z z = 0 := by
  by_contra! h
  have hprojection (z : V) (hzx : B P.x z = 0) (hzz : B z z = 0) :
      z = B P.y z • P.x := by
    let w := ((P.split hS).symm z).2
    have hw : (w : V) = z - B P.y z • P.x := by
      rw [P.split_symm_snd hS, hzx, zero_smul, sub_zero]
    have hzw : B z P.x = 0 := (hS.eq _ _).trans hzx
    have hww : B w w = 0 := by
      rw [hw]
      simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, hzx, hzw,
        P.xx, hzz, smul_zero, sub_zero]
    have hw0 : w = 0 := by by_contra hn; exact h w hn hww
    exact sub_eq_zero.mp (hw.symm.trans (congrArg Subtype.val hw0))
  have hdep (hx' : B P.x x = 0) (hy' : B P.x y = 0) : False := by
    have he : B P.y y • x + (-B P.y x) • y = 0 := by
      conv_lhs =>
        congr
        · rw [hprojection x hx' hx]
        · rw [hprojection y hy' hy]
      rw [smul_smul, smul_smul, neg_mul, mul_comm (B P.y y), neg_smul, add_neg_cancel]
    have h₀ := (LinearIndependent.pair_iff.mp hli) _ _ he
    have h1 : B P.y x = 0 := neg_eq_zero.mp h₀.2
    have hzero : x = 0 := (hprojection x hx' hx).trans (by rw [h1, zero_smul])
    have hx1 : (1 : K) • x + (0 : K) • y = 0 := by rw [hzero, smul_zero, zero_smul, add_zero]
    exact one_ne_zero ((LinearIndependent.pair_iff.mp hli) _ _ hx1).1
  let z := B P.x y • x + (-B P.x x) • y
  have hz0 : z ≠ 0 := fun hz =>
    let hz' := (LinearIndependent.pair_iff.mp hli) _ _ hz
    hdep (neg_eq_zero.mp hz'.2) hz'.1
  have hze : B P.x z = 0 := by
    simp only [z, map_add, map_smul, smul_eq_mul]
    ring
  have hyx : B y x = 0 := (hS.eq _ _).trans hxy
  have hxz : B x z = 0 := by simp [z, hx, hxy]
  have hyz : B y z = 0 := by simp [z, hyx, hy]
  have hzz : B z z = 0 := by
    change B (B P.x y • x + (-B P.x x) • y) z = _
    simp [hxz, hyz]
  have hzeq := hprojection z hze hzz
  have hn : B P.y z ≠ 0 := fun ht => hz0 (hzeq.trans (by rw [ht, zero_smul]))
  have horth (v : V) (hv : B v z = 0) : B P.x v = 0 := by
    have he := congrArg (B v) hzeq
    rw [hv, map_smul, smul_eq_mul, hS.eq v P.x] at he
    exact (mul_eq_zero.mp he.symm).resolve_left hn
  exact hdep (horth x hxz) (horth y hyz)

/-- An isotropic plane leaves an isotropic vector in the complement of any
  hyperbolic plane. -/
def IsotropicPlaneOrthogonalComplementStatement : Prop :=
  ∀ (K : Type u) [Field K] (V : Type v) [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (P : HyperbolicPair B), B.IsSymm →
    ∀ x y : V, LinearIndependent K ![x, y] → B x x = 0 → B x y = 0 → B y y = 0 →
      ∃ z : P.orthogonalComplement, z ≠ 0 ∧ B z z = 0

theorem isotropicPlaneOrthogonalComplement : IsotropicPlaneOrthogonalComplementStatement.{u, v} := by
  intro K _ V _ _ B P hS x y hli hx hxy hy
  exact P.exists_isotropic_in_complement_of_plane hS hli hx hxy hy

end Langlands.SymmetricBilinear.HyperbolicPair
