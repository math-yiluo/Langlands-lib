import Langlands.LinearAlgebra.IsotropicPlaneOrthogonalComplement
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-! # Opposite binary subforms in an orthogonal sum with an isotropic plane -/

noncomputable section

universe u v w

namespace Langlands.SymmetricBilinear

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000

section Pair

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {B : LinearMap.BilinForm K V}

/-- In the plane of a normalized hyperbolic pair, the row with coordinates
  `1, a/2` has self-pairing `a`. -/
theorem HyperbolicPair.represents_value (P : HyperbolicPair B) (hB : B.IsSymm)
    (h2 : (2 : K) ≠ 0) (a : K) :
    B (P.split hB ((1, a / 2), 0)) (P.split hB ((1, a / 2), 0)) = a := by
  rw [P.split_pairing]
  simp only [one_mul, mul_one, Submodule.coe_zero, map_zero, add_zero]
  rw [← two_mul, mul_comm, div_mul_cancel₀ _ h2]

private theorem exists_orthogonal_ne_zero [FiniteDimensional K V] (hdim : 2 ≤ Module.finrank K V)
    (x : V) : ∃ y, y ≠ 0 ∧ B x y = 0 := by
  have h := (B x).finrank_range_add_finrank_ker
  have h₁ : Module.finrank K (LinearMap.range (B x)) ≤ 1 := by
    simpa only [Module.finrank_self] using (LinearMap.range (B x)).finrank_le
  have h₂ : LinearMap.ker (B x) ≠ ⊥ := by
    intro hz
    rw [hz, finrank_bot, add_zero] at h
    omega
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h₂
  exact ⟨y, hy0, hy⟩

end Pair

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  (B : LinearMap.BilinForm K V) (C : LinearMap.BilinForm K W)

/-- The direct sum pairing with the two factors orthogonal. -/
def orthogonalSum : LinearMap.BilinForm K (V × W) :=
  B.compl₁₂ (LinearMap.fst K V W) (LinearMap.fst K V W) +
  C.compl₁₂ (LinearMap.snd K V W) (LinearMap.snd K V W)

@[simp] theorem orthogonalSum_apply (x y : V × W) :
    orthogonalSum B C x y = B x.1 y.1 + C x.2 y.2 := rfl

private theorem orthogonalSum_isSymm (hB : B.IsSymm) (hC : C.IsSymm) :
    (orthogonalSum B C).IsSymm :=
  ⟨fun x y => by simp only [orthogonalSum_apply, hB.eq x.1 y.1, hC.eq x.2 y.2]⟩

/-- Opposite nonsingular two-dimensional subforms in orthogonal bases. -/
def HasOppositeBinarySubforms : Prop :=
  ∃ x y : V, ∃ a b : W, B x x ≠ 0 ∧ B y y ≠ 0 ∧ B x y = 0 ∧ C a b = 0 ∧
    B x x + C a a = 0 ∧ B y y + C b b = 0

private theorem HasOppositeBinarySubforms.symm {B : LinearMap.BilinForm K V} {C : LinearMap.BilinForm K W}
    (h : HasOppositeBinarySubforms B C) : HasOppositeBinarySubforms C B := by
  obtain ⟨x, y, a, b, hx, hy, hxy, hab, ha, hb⟩ := h
  refine ⟨a, b, x, y, ?_, ?_, hab, hxy, (add_comm _ _).trans ha, (add_comm _ _).trans hb⟩
  · exact fun h => hx (by simpa only [h, add_zero] using ha)
  · exact fun h => hy (by simpa only [h, add_zero] using hb)

private theorem opposite_of_anisotropic (hB : B.toQuadraticMap.Anisotropic)
    (hC : C.toQuadraticMap.Anisotropic) (hBs : B.IsSymm) (hCs : C.IsSymm) {x y : V × W}
    (hli : LinearIndependent K ![x, y]) (hx : orthogonalSum B C x x = 0)
    (hxy : orthogonalSum B C x y = 0) (hy : orthogonalSum B C y y = 0) :
    HasOppositeBinarySubforms B C := by
  have posLeft {z : V × W} (hz : z ≠ 0) (hzq : orthogonalSum B C z z = 0) :
      B z.1 z.1 ≠ 0 := by
    intro he
    have hc : C z.2 z.2 = 0 := by simpa only [orthogonalSum_apply, he, zero_add] using hzq
    exact hz (Prod.ext (hB _ he) (hC _ hc))
  have hx0 : x ≠ 0 := fun h =>
    one_ne_zero ((LinearIndependent.pair_iff.mp hli) 1 0 (by rw [h, smul_zero, zero_smul, add_zero])).1
  have hxx := posLeft hx0 hx
  let s := B x.1 y.1 / B x.1 x.1
  let z := y - s • x
  have hz : z ≠ 0 := by
    intro h
    have e : (-s) • x + (1 : K) • y = 0 := by rw [one_smul, neg_smul, add_comm, ← sub_eq_add_neg]; exact h
    exact one_ne_zero ((LinearIndependent.pair_iff.mp hli) _ _ e).2
  let T := orthogonalSum B C
  have hxz : T x z = 0 := by
    change T x (y - s • x) = _
    rw [map_sub, map_smul, show T x x = 0 from hx, show T x y = 0 from hxy, smul_zero, sub_zero]
  have hyx : T y x = 0 := ((orthogonalSum_isSymm B C hBs hCs).eq y x).trans hxy
  have hzz : T z z = 0 := by
    change T (y - s • x) (y - s • x) = _
    simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
      show T y x = 0 from hyx, show T y y = 0 from hy, show T x y = 0 from hxy,
      show T x x = 0 from hx, smul_zero, sub_zero]
  have hb : B x.1 z.1 = 0 := by
    change B x.1 (y.1 - s • x.1) = _
    rw [map_sub, map_smul, smul_eq_mul, show s = B x.1 y.1 / B x.1 x.1 from rfl,
      div_mul_cancel₀ _ hxx, sub_self]
  have hc : C x.2 z.2 = 0 := by simpa only [T, orthogonalSum_apply, hb, zero_add] using hxz
  exact ⟨x.1, z.1, x.2, z.2, hxx, posLeft hz hzz, hb, hc, hx, hzz⟩

private theorem opposite_of_hyperbolic_pairs (P : HyperbolicPair B) (Q : HyperbolicPair C)
    (hB : B.IsSymm) (hC : C.IsSymm) (h2 : (2 : K) ≠ 0) : HasOppositeBinarySubforms B C := by
  let x := P.split hB ((1, 1 / 2), 0)
  let y := P.split hB ((1, -1 / 2), 0)
  let a := Q.split hC ((1, -1 / 2), 0)
  let b := Q.split hC ((1, 1 / 2), 0)
  have hx : B x x = 1 := P.represents_value hB h2 1
  have hy : B y y = -1 := P.represents_value hB h2 (-1)
  have ha : C a a = -1 := Q.represents_value hC h2 (-1)
  have hb : C b b = 1 := Q.represents_value hC h2 1
  refine ⟨x, y, a, b, hx.trans_ne one_ne_zero, hy.trans_ne (neg_ne_zero.mpr one_ne_zero),
    ?_, ?_, by rw [hx, ha, add_neg_cancel], by rw [hy, hb, neg_add_cancel]⟩
  · change B (P.split hB ((1, 1 / 2), 0)) (P.split hB ((1, -1 / 2), 0)) = 0
    rw [P.split_pairing]
    simp [neg_div]
  · change C (Q.split hC ((1, -1 / 2), 0)) (Q.split hC ((1, 1 / 2), 0)) = 0
    rw [Q.split_pairing]
    simp [neg_div]

private theorem opposite_of_left_hyperbolic [FiniteDimensional K W]
    (hB : B.IsSymm) (hC : C.IsSymm) (hBnd : B.Nondegenerate)
    (h2 : (2 : K) ≠ 0) (hW : 2 ≤ Module.finrank K W) (P : HyperbolicPair B)
    (hCa : C.toQuadraticMap.Anisotropic) {x y : V × W}
    (hli : LinearIndependent K ![x, y]) (hx : orthogonalSum B C x x = 0)
    (hxy : orthogonalSum B C x y = 0) (hy : orthogonalSum B C y y = 0) :
    HasOppositeBinarySubforms B C := by
  let T := orthogonalSum B C
  let P' : HyperbolicPair T := ⟨(P.x, 0), (P.y, 0), by simp [T, P.xx], by simp [T, P.xy],
    by simp [T, P.yy]⟩
  obtain ⟨z, hz, hzz⟩ := P'.exists_isotropic_in_complement_of_plane (orthogonalSum_isSymm B C hB hC)
    hli hx hxy hy
  let U := P.orthogonalComplement
  let z₁ := (z : V × W).1
  let z₂ := (z : V × W).2
  have hz₁ : z₁ ∈ U := by
    have h := (P'.mem_orthogonalComplement (z : V × W)).mp z.property
    change B P.x z₁ = 0 ∧ B P.y z₁ = 0
    simpa only [T, P', orthogonalSum_apply, map_zero, LinearMap.zero_apply, add_zero] using h
  have hsum : B z₁ z₁ + C z₂ z₂ = 0 := hzz
  have hline : ∃ (r : U) (t : W), t ≠ 0 ∧ B r r + C t t = 0 := by
    by_cases ht : z₂ = 0
    · have hz1 : (⟨z₁, hz₁⟩ : U) ≠ 0 := by
        intro he
        exact hz (Subtype.ext (Prod.ext (congrArg Subtype.val he) ht))
      have hz0 : B z₁ z₁ = 0 := by simpa only [ht, map_zero, add_zero] using hsum
      let B₀ := B.restrict U
      have hB₀ : B₀.IsSymm := ⟨fun a b => hB.eq (a : V) (b : V)⟩
      obtain ⟨Q, _⟩ := HyperbolicPair.exists_with_first hB₀ (P.nondegenerate_restrict hB hBnd)
        h2 ⟨z₁, hz₁⟩ hz1 hz0
      let : Nontrivial W := Module.nontrivial_of_finrank_pos (show 0 < Module.finrank K W by omega)
      obtain ⟨t, ht0⟩ := exists_ne (0 : W)
      let r := Q.split hB₀ ((1, -(C t t) / 2), 0)
      have hr : B r r = -(C t t) := Q.represents_value hB₀ h2 (-(C t t))
      exact ⟨r, t, ht0, hr ▸ neg_add_cancel _⟩
    · exact ⟨⟨z₁, hz₁⟩, z₂, ht, hsum⟩
  obtain ⟨r, t, ht, hrt⟩ := hline
  obtain ⟨b, hb, htb⟩ := exists_orthogonal_ne_zero (B := C) hW t
  let a := P.split hB ((1, -(C b b) / 2), 0)
  have ha : B a a = -(C b b) := P.represents_value hB h2 _
  have hra : B r a = 0 := by
    have hr : P.split hB ((0, 0), r) = (r : V) := by simp
    change B r (P.split hB ((1, -(C b b) / 2), 0)) = 0
    rw [← hr, P.split_pairing]
    simp
  refine ⟨r, a, t, b, ?_, ?_, hra, htb, hrt, by rw [ha, neg_add_cancel]⟩
  · intro he
    have ht0 : C t t = 0 := by simpa only [he, zero_add] using hrt
    exact ht (hCa t ht0)
  · exact ha.trans_ne (neg_ne_zero.mpr (fun he => hb (hCa b he)))

/-- If the orthogonal sum of two nonsingular symmetric forms contains a totally
  isotropic plane, both forms contain opposite regular binary subforms. -/
def OppositeBinarySubformsStatement : Prop :=
  ∀ (K : Type u) [Field K], (2 : K) ≠ 0 →
    ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (W : Type w) [AddCommGroup W] [Module K W] [FiniteDimensional K W]
      (B : LinearMap.BilinForm K V) (C : LinearMap.BilinForm K W),
      B.IsSymm → C.IsSymm → B.Nondegenerate → C.Nondegenerate →
      2 ≤ Module.finrank K V → 2 ≤ Module.finrank K W →
      ∀ x y : V × W, LinearIndependent K ![x, y] →
      orthogonalSum B C x x = 0 → orthogonalSum B C x y = 0 → orthogonalSum B C y y = 0 →
      HasOppositeBinarySubforms B C

theorem oppositeBinarySubforms : OppositeBinarySubformsStatement.{u, v, w} := by
  classical
  intro K _ h2 V _ _ _ W _ _ _ B C hB hC hBnd hCnd hV hW x y hli hx hxy hy
  by_cases hb : B.toQuadraticMap.Anisotropic
  · by_cases hc : C.toQuadraticMap.Anisotropic
    · exact opposite_of_anisotropic B C hb hc hB hC hli hx hxy hy
    · obtain ⟨e, he, hee⟩ := (QuadraticMap.not_anisotropic_iff_exists _).mp hc
      obtain ⟨P, _⟩ := HyperbolicPair.exists_with_first hC hCnd h2 e he hee
      let j := LinearEquiv.prodComm K V W
      have hj : LinearIndependent K ![j x, j y] := by
        have hjmap : j.toLinearMap ∘ ![x, y] = ![j x, j y] := by
          funext i
          fin_cases i <;> rfl
        rw [← hjmap]
        exact hli.map' j.toLinearMap (LinearMap.ker_eq_bot.mpr j.injective)
      have hswap (u v : V × W) : orthogonalSum C B (j u) (j v) = orthogonalSum B C u v := by
        change C u.2 v.2 + B u.1 v.1 = _
        exact add_comm _ _
      exact (opposite_of_left_hyperbolic C B hC hB hCnd h2 hV P hb hj
        ((hswap x x).trans hx) ((hswap x y).trans hxy) ((hswap y y).trans hy)).symm
  · obtain ⟨e, he, hee⟩ := (QuadraticMap.not_anisotropic_iff_exists _).mp hb
    obtain ⟨P, _⟩ := HyperbolicPair.exists_with_first hB hBnd h2 e he hee
    by_cases hc : C.toQuadraticMap.Anisotropic
    · exact opposite_of_left_hyperbolic B C hB hC hBnd h2 hW P hc hli hx hxy hy
    · obtain ⟨e', he', hee'⟩ := (QuadraticMap.not_anisotropic_iff_exists _).mp hc
      obtain ⟨Q, _⟩ := HyperbolicPair.exists_with_first hC hCnd h2 e' he' hee'
      exact opposite_of_hyperbolic_pairs B C P Q hB hC h2

end Langlands.SymmetricBilinear
