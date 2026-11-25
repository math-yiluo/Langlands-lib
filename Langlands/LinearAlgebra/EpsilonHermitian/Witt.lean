import Langlands.LinearAlgebra.EpsilonHermitian.Lagrangian
import Mathlib.Tactic.NoncommRing

/-!
# Witt's theorem

GKT Appendix B.2.1: Theorem B.11 (Witt decomposition), Definition B.12, Theorem B.15
(diagonalization), Theorem B.17 (Witt's extension theorem); Lemma 4.10 (b) with Definition 4.7.

The book cites Scharlau, *Quadratic and Hermitian Forms*, Chapter 7, Theorem 9.5 (p. 269) for
Theorem B.17. Scharlau proves it there with reflections, by induction on `dim W + 2 dim (W ∩ W^⊥)`,
excluding the alternating case; the same induction is carried out here for every `ε` and every
involution, the alternating case (`IsAlternatingCase`: `ε = -1` and `τ` trivial) being treated
with symplectic transvections.

* `reflection x β`: for `h x x ≠ 0` and `β h(x,x) β^τ = h(x,x)`, the isometry
  `y ↦ y + h(y,x) h(x,x)⁻¹ (β - 1) x` fixing `x^⊥` and sending `x` to `β x` (Scharlau 7.9.3,
  7.9.4);
* `exists_isometry_map_of_apply_self_eq`: two vectors with the same non-zero value `h(x,x)` are
  exchanged by an isometry fixing their common orthogonal;
* `transvection v a` (alternating case): `w ↦ w + a h(w,v) v`;
* `exists_isometry_extend_of_injective` (Theorem B.17): an injective form-preserving linear map
  from a subspace into a non-degenerate space extends to an isometry.
-/

noncomputable section

namespace Langlands

namespace EpsilonHermitianForm

open Module
open Langlands.RingInvo (conj conj_conj)

variable {D : Type*} [DivisionRing D] {τ : _root_.RingInvo D} {ε : ℤˣ}
  {V : Type*} [AddCommGroup V] [Module D V] {h : EpsilonHermitianForm τ ε V}

/-! ### The alternating case -/

variable (τ ε) in
/-- The alternating (symplectic) case: `ε = -1` and the involution is trivial (GKT B.15:
"`τ` trivial and `ε = -`"). Only then can a non-zero form have only isotropic vectors. -/
def IsAlternatingCase : Prop := ε = -1 ∧ ∀ d : D, conj τ d = d

theorem IsAlternatingCase.mul_comm (hA : IsAlternatingCase τ ε) (a b : D) : a * b = b * a := by
  have := RingInvo.conj_mul τ a b
  rwa [hA.2, hA.2, hA.2] at this

theorem IsAlternatingCase.intCast (hA : IsAlternatingCase τ ε) : ((ε : ℤ) : D) = -1 := by
  rw [hA.1]; simp

theorem IsAlternatingCase.apply_swap (hA : IsAlternatingCase τ ε) (x y : V) :
    h y x = -h x y := by
  rw [h.conj_swap, hA.2, hA.intCast, neg_one_mul]

theorem IsAlternatingCase.apply_self [NeZero (2 : D)] (hA : IsAlternatingCase τ ε) (x : V) :
    h x x = 0 := by
  have e := hA.apply_swap (h := h) x x
  have : (2 : D) * h x x = 0 := by rw [two_mul]; nth_rewrite 1 [e]; rw [neg_add_cancel]
  exact (mul_eq_zero.1 this).resolve_left (NeZero.ne 2)

/-- If every vector of a subspace is isotropic but the form does not vanish on it, we are in the
alternating case. -/
theorem isAlternatingCase_of_apply_self [NeZero (2 : D)] {U : Submodule D V}
    (hall : ∀ x ∈ U, h x x = 0) {x y : V} (hx : x ∈ U) (hy : y ∈ U) (hxy : h x y ≠ 0) :
    IsAlternatingCase τ ε := by
  have hpol : ∀ a ∈ U, ∀ b ∈ U, h b a = -h a b := fun a ha b hb => by
    have := hall (a + b) (U.add_mem ha hb)
    rw [h.map_add_left, h.map_add_right, h.map_add_right, hall a ha, hall b hb, zero_add,
      add_zero] at this
    exact eq_neg_of_add_eq_zero_right this
  set c := h x y
  -- `d c = c d^τ` for all `d`
  have hd : ∀ d : D, d * c = c * conj τ d := fun d => by
    have e := hpol (d • x) (U.smul_mem d hx) y hy
    rw [h.map_smul_left, h.map_smul_right, hpol x hx y hy, neg_mul, neg_inj] at e
    exact e.symm
  -- the involution is the inner automorphism `d ↦ c⁻¹ d c`, hence multiplicative, hence trivial
  have hconj : ∀ d : D, conj τ d = c⁻¹ * d * c := fun d => by
    rw [mul_assoc, hd d, ← mul_assoc, inv_mul_cancel₀ hxy, one_mul]
  have hcomm : ∀ a b : D, a * b = b * a := fun a b => by
    have e := RingInvo.conj_mul τ a b
    rw [hconj, hconj, hconj] at e
    have e2 : c⁻¹ * ((a * b) * c) = c⁻¹ * ((b * a) * c) := by
      have : c⁻¹ * b * c * (c⁻¹ * a * c) = c⁻¹ * (b * a * c) := by
        simp only [mul_assoc, mul_inv_cancel_left₀ hxy]
      rw [← mul_assoc, e, this]
    exact mul_right_cancel₀ hxy (mul_left_cancel₀ (inv_ne_zero hxy) e2)
  have htriv : ∀ d : D, conj τ d = d := fun d => by
    rw [hconj, hcomm c⁻¹ d, mul_assoc, inv_mul_cancel₀ hxy, mul_one]
  refine ⟨?_, htriv⟩
  have e := h.conj_swap x y
  rw [hpol x hx y hy, htriv] at e
  rcases Int.units_eq_one_or ε with hε | hε
  · exfalso
    have h1 : ((ε : ℤ) : D) = 1 := by rw [hε]; simp
    rw [h1, one_mul] at e
    have : (2 : D) * h x y = 0 := by
      calc (2 : D) * h x y = h x y + h x y := two_mul _
        _ = -h x y + h x y := by rw [e]
        _ = 0 := neg_add_cancel _
    exact hxy ((mul_eq_zero.1 this).resolve_left (NeZero.ne 2))
  · exact hε

/-! ### Reflections (Scharlau 7.9.3, 7.9.4) -/

section Reflection

variable (h) in
/-- The map `y ↦ y + h(y,x) h(x,x)⁻¹ (β - 1) x`. -/
def reflectionMap (x : V) (β : D) : V →ₗ[D] V where
  toFun y := y + (h y x * (h x x)⁻¹ * (β - 1)) • x
  map_add' a b := by
    rw [h.map_add_left, add_mul, add_mul, add_smul]; abel
  map_smul' c a := by
    rw [h.map_smul_left, mul_assoc, mul_assoc, ← smul_smul, smul_add, RingHom.id_apply,
      ← mul_assoc]

theorem reflectionMap_apply (x : V) (β : D) (y : V) :
    h.reflectionMap x β y = y + (h y x * (h x x)⁻¹ * (β - 1)) • x := rfl

/-- The value of the form on `y₀ + a x`, `y₀' + a' x` with `y₀, y₀' ⊥ x`. -/
private theorem apply_add_smul {x y₀ y₀' : V} (h0 : h y₀ x = 0) (h0' : h x y₀' = 0) (a a' : D) :
    h (y₀ + a • x) (y₀' + a' • x) = h y₀ y₀' + a * h x x * conj τ a' := by
  rw [h.map_add_left, h.map_add_right, h.map_add_right, h.map_smul_left, h.map_smul_left,
    h.map_smul_right, h.map_smul_right, h0, h0', zero_mul, mul_zero, zero_add, add_zero,
    mul_assoc]

theorem reflectionMap_map_apply {x : V} (hx : h x x ≠ 0) {β : D}
    (hβ : β * h x x * conj τ β = h x x) (y y' : V) :
    h (h.reflectionMap x β y) (h.reflectionMap x β y') = h y y' := by
  set c := h x x
  set l : V → D := fun v => h v x * c⁻¹
  have hdec : ∀ v, v = (v - l v • x) + l v • x := fun v => by rw [sub_add_cancel]
  have horth : ∀ v, h (v - l v • x) x = 0 := fun v => by
    rw [h.map_sub_left, h.map_smul_left, mul_assoc, inv_mul_cancel₀ hx, mul_one, sub_self]
  have horth' : ∀ v, h x (v - l v • x) = 0 := fun v => (h.apply_eq_zero_comm).1 (horth v)
  have hr : ∀ v, h.reflectionMap x β v = (v - l v • x) + (l v * β) • x := fun v => by
    rw [reflectionMap_apply]
    simp only [l, mul_sub, mul_one, sub_smul]
    abel
  rw [hr, hr, apply_add_smul (horth y) (horth' y'), RingInvo.conj_mul]
  conv_rhs => rw [hdec y, hdec y', apply_add_smul (horth y) (horth' y')]
  congr 1
  calc l y * β * c * (conj τ β * conj τ (l y')) = l y * (β * c * conj τ β) * conj τ (l y') := by
        noncomm_ring
    _ = _ := by rw [hβ]

/-- The reflection `y ↦ y + h(y,x) h(x,x)⁻¹ (β - 1) x` for an anisotropic `x` and
`β h(x,x) β^τ = h(x,x)`, an isometry (Scharlau 7.9.3). -/
def reflection [FiniteDimensional D V] (hh : h.Nondegenerate) {x : V} (hx : h x x ≠ 0) {β : D}
    (hβ : β * h x x * conj τ β = h x x) : h.isometryGroup :=
  ofLinearMap hh (h.reflectionMap x β) (reflectionMap_map_apply hx hβ)

theorem reflection_apply [FiniteDimensional D V] (hh : h.Nondegenerate) {x : V}
    (hx : h x x ≠ 0) {β : D} (hβ : β * h x x * conj τ β = h x x) (y : V) :
    ((reflection hh hx hβ : h.isometryGroup) : V ≃ₗ[D] V) y =
      y + (h y x * (h x x)⁻¹ * (β - 1)) • x := rfl

theorem reflection_apply_of_orthogonal [FiniteDimensional D V] (hh : h.Nondegenerate) {x : V}
    (hx : h x x ≠ 0) {β : D} (hβ : β * h x x * conj τ β = h x x) {y : V} (hy : h y x = 0) :
    ((reflection hh hx hβ : h.isometryGroup) : V ≃ₗ[D] V) y = y := by
  rw [reflection_apply, hy, zero_mul, zero_mul, zero_smul, add_zero]

/-- The reflection with `β = -1` sends `x` to `-x`. -/
theorem neg_one_mul_apply_self_mul_neg_one (x : V) :
    (-1 : D) * h x x * conj τ (-1) = h x x := by
  rw [RingInvo.conj_neg, RingInvo.conj_one]; noncomm_ring

/-- The algebra behind Scharlau's choice of `α` in the proof of 7.9.5: if `p + s = q`,
`p^τ = ε s` and `q^τ = ε q`, then `β = 1 - q p⁻¹` satisfies `β q β^τ = q`. -/
private theorem reflection_scalar {p s q : D} (hp : p ≠ 0) (hs : s ≠ 0) (hpsq : p + s = q)
    (hcp : conj τ p = ((ε : ℤ) : D) * s) (hcq : conj τ q = ((ε : ℤ) : D) * q) :
    (1 - q * p⁻¹) * q * conj τ (1 - q * p⁻¹) = q := by
  have hcβ : conj τ (1 - q * p⁻¹) = 1 - s⁻¹ * q := by
    have hεinv : (((ε : ℤ) : D))⁻¹ = ((ε : ℤ) : D) :=
      inv_eq_of_mul_eq_one_left (units_int_cast_mul_self' ε)
    rw [RingInvo.conj_sub, RingInvo.conj_one, RingInvo.conj_mul, RingInvo.conj_inv, hcp, hcq,
      mul_inv_rev, hεinv, mul_assoc, ← mul_assoc ((ε : ℤ) : D), units_int_cast_mul_self',
      one_mul]
  have key : q * p⁻¹ * q * s⁻¹ * q = q * s⁻¹ * q + q * p⁻¹ * q := by
    calc q * p⁻¹ * q * s⁻¹ * q = q * (p⁻¹ * (p + s) * s⁻¹) * q := by rw [hpsq]; noncomm_ring
      _ = q * (s⁻¹ + p⁻¹) * q := by
          rw [mul_add, add_mul, inv_mul_cancel₀ hp, one_mul, mul_assoc p⁻¹ s s⁻¹,
            mul_inv_cancel₀ hs, mul_one]
      _ = _ := by noncomm_ring
  rw [hcβ]
  calc (1 - q * p⁻¹) * q * (1 - s⁻¹ * q)
      = q - q * s⁻¹ * q - q * p⁻¹ * q + q * p⁻¹ * q * s⁻¹ * q := by noncomm_ring
    _ = q := by rw [key]; abel

/-- Two vectors `x`, `y` with `h(x,x) = h(y,y) ≠ 0` such that `x - y` is anisotropic are exchanged
by a reflection in `x - y` (Scharlau 7.9.5, first case). -/
private theorem exists_isometry_map_of_sub [FiniteDimensional D V] (hh : h.Nondegenerate)
    {x y : V} (hxy : h x x = h y y) (hz : h (x - y) (x - y) ≠ 0) :
    ∃ g : h.isometryGroup, (g : V ≃ₗ[D] V) x = y ∧
      ∀ w, h w x = 0 → h w y = 0 → (g : V ≃ₗ[D] V) w = w := by
  set z := x - y
  set p := h x z
  set s := h z x
  set q := h z z
  have hpsq : p + s = q := by
    simp only [p, s, q, z, h.map_sub_left, h.map_sub_right]
    rw [hxy]; abel
  have hcp : conj τ p = ((ε : ℤ) : D) * s := h.conj_apply x z
  have hcq : conj τ q = ((ε : ℤ) : D) * q := h.conj_apply z z
  have hp : p ≠ 0 := by
    intro hp0
    have : s = 0 := by
      have := hcp; rw [hp0, RingInvo.conj_zero] at this
      have h2 := congrArg (((ε : ℤ) : D) * ·) this
      simpa [← mul_assoc, units_int_cast_mul_self'] using h2.symm
    exact hz (by rw [← hpsq, hp0, this, add_zero])
  have hs : s ≠ 0 := by
    intro hs0
    exact hz (by
      have := hcp; rw [hs0, mul_zero, RingInvo.conj_eq_zero_iff] at this
      rw [← hpsq, this, hs0, add_zero])
  refine ⟨reflection hh hz (reflection_scalar hp hs hpsq hcp hcq), ?_, fun w hwx hwy => ?_⟩
  · rw [reflection_apply]
    have : p * q⁻¹ * (1 - q * p⁻¹ - 1) = -1 := by
      rw [sub_sub_cancel_left, mul_neg, mul_assoc, ← mul_assoc q⁻¹, inv_mul_cancel₀ hz, one_mul,
        mul_inv_cancel₀ hp]
    rw [this, neg_one_smul, ← sub_eq_add_neg, sub_sub_cancel]
  · apply reflection_apply_of_orthogonal
    rw [h.map_sub_right, hwx, hwy, sub_zero]

/-- Two vectors with the same non-zero value `h(x,x) = h(y,y)` are exchanged by an isometry fixing
every vector orthogonal to both (Scharlau 7.9.5; `2` is invertible). -/
theorem exists_isometry_map_of_apply_self_eq [FiniteDimensional D V] [NeZero (2 : D)]
    (hh : h.Nondegenerate) {x y : V} (hxy : h x x = h y y) (hx : h x x ≠ 0) :
    ∃ g : h.isometryGroup, (g : V ≃ₗ[D] V) x = y ∧
      ∀ w, h w x = 0 → h w y = 0 → (g : V ≃ₗ[D] V) w = w := by
  by_cases hz : h (x - y) (x - y) = 0
  · -- then `x + y` is anisotropic: map `x` to `-y`, then `-y` to `y`
    have hz' : h (x - -y) (x - -y) ≠ 0 := by
      rw [sub_neg_eq_add]
      intro hz'
      have hsum : h (x + y) (x + y) + h (x - y) (x - y) = 2 * h x x + 2 * h y y := by
        simp only [h.map_add_left, h.map_add_right, h.map_sub_left, h.map_sub_right]
        rw [two_mul, two_mul]; abel
      rw [hz, hz', add_zero, ← hxy, ← mul_add, ← two_mul, ← mul_assoc] at hsum
      have h4 : (2 : D) * 2 ≠ 0 := mul_ne_zero (NeZero.ne 2) (NeZero.ne 2)
      exact hx ((mul_eq_zero.1 hsum.symm).resolve_left h4)
    have hy : h y y ≠ 0 := hxy ▸ hx
    obtain ⟨g₁, hg₁x, hg₁w⟩ := exists_isometry_map_of_sub hh
      (show h x x = h (-y) (-y) by rw [h.map_neg_left, h.map_neg_right, neg_neg, hxy]) hz'
    set g₂ := reflection hh hy (neg_one_mul_apply_self_mul_neg_one (h := h) y)
    refine ⟨g₂ * g₁, ?_, fun w hwx hwy => ?_⟩
    · rw [isometryGroup_coe_mul_apply, hg₁x, map_neg, reflection_apply, mul_inv_cancel₀ hy,
        one_mul, sub_eq_add_neg, ← neg_add, one_add_one_eq_two, neg_smul, two_smul]
      abel
    · rw [isometryGroup_coe_mul_apply, hg₁w w hwx (by rw [h.map_neg_right, hwy, neg_zero])]
      exact reflection_apply_of_orthogonal hh hy _ hwy
  · exact exists_isometry_map_of_sub hh hxy hz

end Reflection

/-! ### Transvections in the alternating case -/

section Transvection

variable (h) in
/-- The map `w ↦ w + h(w,v) a v`. -/
def transvectionMap (v : V) (a : D) : V →ₗ[D] V where
  toFun w := w + (h w v * a) • v
  map_add' w w' := by rw [h.map_add_left, add_mul, add_smul]; abel
  map_smul' c w := by
    rw [h.map_smul_left, smul_add, RingHom.id_apply, smul_smul, mul_assoc]

theorem transvectionMap_apply (v : V) (a : D) (w : V) :
    h.transvectionMap v a w = w + (h w v * a) • v := rfl

theorem transvectionMap_map_apply [NeZero (2 : D)] (hA : IsAlternatingCase τ ε) (v : V) (a : D)
    (w w' : V) :
    h (h.transvectionMap v a w) (h.transvectionMap v a w') = h w w' := by
  simp only [transvectionMap_apply, h.map_add_left, h.map_add_right, h.map_smul_left,
    h.map_smul_right, hA.apply_self (h := h) v, hA.2, mul_zero, zero_mul, add_zero]
  rw [hA.apply_swap (h := h) w' v, hA.mul_comm (h w' v) a]
  noncomm_ring

/-- The transvection `w ↦ w + a h(w,v) v` of the alternating case. -/
def transvection [FiniteDimensional D V] [NeZero (2 : D)] (hh : h.Nondegenerate)
    (hA : IsAlternatingCase τ ε) (v : V) (a : D) : h.isometryGroup :=
  ofLinearMap hh (h.transvectionMap v a) (transvectionMap_map_apply hA v a)

theorem transvection_apply [FiniteDimensional D V] [NeZero (2 : D)] (hh : h.Nondegenerate)
    (hA : IsAlternatingCase τ ε) (v : V) (a : D) (w : V) :
    ((transvection hh hA v a : h.isometryGroup) : V ≃ₗ[D] V) w = w + (h w v * a) • v := rfl

/-- In the alternating case, `u ↦ u'` by a transvection fixing `(u' - u)^⊥`, when
`h(u, u') ≠ 0`. -/
private theorem exists_transvection_map [FiniteDimensional D V] [NeZero (2 : D)]
    (hh : h.Nondegenerate) (hA : IsAlternatingCase τ ε) {u u' : V} (hu : h u u' ≠ 0) :
    ∃ g : h.isometryGroup, (g : V ≃ₗ[D] V) u = u' ∧
      ∀ w, h w (u' - u) = 0 → (g : V ≃ₗ[D] V) w = w := by
  refine ⟨transvection hh hA (u' - u) (h u u')⁻¹, ?_, fun w hw => ?_⟩
  · rw [transvection_apply, h.map_sub_right, hA.apply_self (h := h) u, sub_zero,
      mul_inv_cancel₀ hu, one_smul, add_sub_cancel]
  · rw [transvection_apply, hw, zero_mul, zero_smul, add_zero]

private theorem exists_transvection_map' [FiniteDimensional D V] [NeZero (2 : D)]
    (hh : h.Nondegenerate) (hA : IsAlternatingCase τ ε) {u u' : V} (hu : h u u' ≠ 0) :
    ∃ g : h.isometryGroup, (g : V ≃ₗ[D] V) u = u' ∧
      ∀ w, h w u = 0 → h w u' = 0 → (g : V ≃ₗ[D] V) w = w := by
  obtain ⟨g, hg, hgw⟩ := exists_transvection_map hh hA hu
  exact ⟨g, hg, fun w h1 h2 => hgw w (by rw [h.map_sub_right, h1, h2, sub_zero])⟩

/-- In the alternating case, two hyperbolic pairs are exchanged by an isometry fixing every vector
orthogonal to the four vectors. -/
theorem exists_isometry_map_isHyperbolicPair [FiniteDimensional D V] [NeZero (2 : D)]
    (hh : h.Nondegenerate) (hA : IsAlternatingCase τ ε) {x y x' y' : V}
    (hp : h.IsHyperbolicPair x y) (hp' : h.IsHyperbolicPair x' y') :
    ∃ g : h.isometryGroup, (g : V ≃ₗ[D] V) x = x' ∧ (g : V ≃ₗ[D] V) y = y' ∧
      ∀ w, h w x = 0 → h w y = 0 → h w x' = 0 → h w y' = 0 → (g : V ≃ₗ[D] V) w = w := by
  have hswap := hA.apply_swap (h := h)
  have h1ne : (-1 : D) ≠ 0 := neg_ne_zero.2 one_ne_zero
  -- step 1: an isometry `g₁` with `g₁ x = x'`, fixing `{x, y, x', y'}^⊥`
  obtain ⟨g₁, hg₁x, hg₁w⟩ : ∃ g₁ : h.isometryGroup, (g₁ : V ≃ₗ[D] V) x = x' ∧
      ∀ w, h w x = 0 → h w y = 0 → h w x' = 0 → h w y' = 0 → (g₁ : V ≃ₗ[D] V) w = w := by
    by_cases hxx' : h x x' ≠ 0
    · obtain ⟨g, hg, hgw⟩ := exists_transvection_map' hh hA hxx'
      exact ⟨g, hg, fun w h1 _ h3 _ => hgw w h1 h3⟩
    push Not at hxx'
    -- an intermediate vector `z ∈ span {y, y'}` with `h(x, z) ≠ 0 ≠ h(z, x')`
    obtain ⟨z, hxz, hzx', hzw⟩ : ∃ z, h x z ≠ 0 ∧ h z x' ≠ 0 ∧
        ∀ w, h w y = 0 → h w y' = 0 → h w z = 0 := by
      by_cases hyx' : h y x' ≠ 0
      · exact ⟨y, by rw [hp.2.2]; exact one_ne_zero, hyx', fun w hy _ => hy⟩
      push Not at hyx'
      by_cases hxy' : h x y' ≠ 0
      · refine ⟨y', hxy', ?_, fun w _ hy' => hy'⟩
        rw [hswap, hp'.2.2]; exact h1ne
      push Not at hxy'
      refine ⟨y + y', ?_, ?_, fun w hy hy' => by rw [h.map_add_right, hy, hy', add_zero]⟩
      · rw [h.map_add_right, hp.2.2, hxy', add_zero]; exact one_ne_zero
      · rw [h.map_add_left, hyx', hswap x' y', hp'.2.2, zero_add]; exact h1ne
    obtain ⟨g, hg, hgw⟩ := exists_transvection_map' hh hA hxz
    obtain ⟨g', hg', hg'w⟩ := exists_transvection_map' hh hA hzx'
    refine ⟨g' * g, by rw [isometryGroup_coe_mul_apply, hg, hg'], fun w h1 h2 h3 h4 => ?_⟩
    rw [isometryGroup_coe_mul_apply, hgw w h1 (hzw w h2 h4), hg'w w (hzw w h2 h4) h3]
  -- step 2: send `y₁ = g₁ y` to `y'`, fixing `x'`
  set y₁ := (g₁ : V ≃ₗ[D] V) y
  have hx'y₁ : h x' y₁ = 1 := by rw [← hg₁x, isometryGroup_apply, hp.2.2]
  have hy₁y₁ : h y₁ y₁ = 0 := hA.apply_self y₁
  have hy₁w : ∀ w, h w x = 0 → h w y = 0 → h w x' = 0 → h w y' = 0 → h w y₁ = 0 :=
    fun w h1 h2 h3 h4 => by rw [← hg₁w w h1 h2 h3 h4, isometryGroup_apply, h2]
  obtain ⟨g₂, hg₂y, hg₂x', hg₂w⟩ : ∃ g₂ : h.isometryGroup, (g₂ : V ≃ₗ[D] V) y₁ = y' ∧
      (g₂ : V ≃ₗ[D] V) x' = x' ∧
      ∀ w, h w y₁ = 0 → h w x' = 0 → h w y' = 0 → (g₂ : V ≃ₗ[D] V) w = w := by
    by_cases hy₁y' : h y₁ y' ≠ 0
    · obtain ⟨g, hg, hgw⟩ := exists_transvection_map hh hA hy₁y'
      refine ⟨g, hg, hgw x' (by rw [h.map_sub_right, hp'.2.2, hx'y₁, sub_self]),
        fun w h1 _ h3 => hgw w (by rw [h.map_sub_right, h1, h3, sub_zero])⟩
    push Not at hy₁y'
    set z := x' + y₁
    have hy₁z : h y₁ z ≠ 0 := by
      rw [h.map_add_right, hswap x' y₁, hx'y₁, hy₁y₁, add_zero]; exact h1ne
    have hzy' : h z y' ≠ 0 := by
      rw [h.map_add_left, hp'.2.2, hy₁y', add_zero]; exact one_ne_zero
    obtain ⟨g, hg, hgw⟩ := exists_transvection_map hh hA hy₁z
    obtain ⟨g', hg', hg'w⟩ := exists_transvection_map hh hA hzy'
    have hzy₁ : z - y₁ = x' := by rw [add_sub_cancel_right]
    have hx'v : h x' (y' - z) = 0 := by
      rw [h.map_sub_right, h.map_add_right, hp'.1, hp'.2.2, hx'y₁, zero_add, sub_self]
    refine ⟨g' * g, by rw [isometryGroup_coe_mul_apply, hg, hg'], ?_, fun w h1 h2 h3 => ?_⟩
    · rw [isometryGroup_coe_mul_apply, hgw x' (by rw [hzy₁, hp'.1]), hg'w x' hx'v]
    · rw [isometryGroup_coe_mul_apply, hgw w (by rw [hzy₁, h2])]
      exact hg'w w (by rw [h.map_sub_right, h.map_add_right, h1, h2, h3, add_zero, sub_zero])
  refine ⟨g₂ * g₁, by rw [isometryGroup_coe_mul_apply, hg₁x, hg₂x'],
    by rw [isometryGroup_coe_mul_apply, hg₂y], fun w h1 h2 h3 h4 => ?_⟩
  rw [isometryGroup_coe_mul_apply, hg₁w w h1 h2 h3 h4]
  exact hg₂w w (hy₁w w h1 h2 h3 h4) h3 h4

end Transvection

/-- Splitting off an anisotropic vector: `U = D x ⊕ (U ∩ x^⊥)`, so `dim (U ∩ x^⊥) + 1 = dim U`. -/
theorem finrank_inf_orthogonal_span_singleton_add_one [FiniteDimensional D V] {U : Submodule D V}
    {x : V} (hxU : x ∈ U) (hx : h x x ≠ 0) :
    finrank D (U ⊓ h.orthogonal (D ∙ x) : Submodule D V) + 1 = finrank D U := by
  set U₁ := U ⊓ h.orthogonal (D ∙ x)
  set l : V → D := fun v => h v x * (h x x)⁻¹
  have hdecomp : ∀ u ∈ U, u - l u • x ∈ U₁ := fun u hu =>
    Submodule.mem_inf.2 ⟨U.sub_mem hu (U.smul_mem _ hxU), by
      rw [mem_orthogonal_span_singleton, h.map_sub_left, h.map_smul_left, mul_assoc,
        inv_mul_cancel₀ hx, mul_one, sub_self]⟩
  have hx0 : x ≠ 0 := fun e => hx (by rw [e, map_zero_left])
  have hsup : (D ∙ x) ⊔ U₁ = U := le_antisymm
    (sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 hxU) inf_le_left) (fun u hu => by
      have := Submodule.add_mem_sup
        (Submodule.mem_span_singleton.2 ⟨l u, rfl⟩ : l u • x ∈ D ∙ x) (hdecomp u hu)
      rwa [add_sub_cancel] at this)
  have hinf : (D ∙ x) ⊓ U₁ = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf] at hv
    obtain ⟨hv, hv2⟩ := hv
    have hv' : h v x = 0 := mem_orthogonal_span_singleton.1 hv2.2
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hv
    rw [h.map_smul_left] at hv'
    have : a = 0 := (mul_eq_zero.1 hv').resolve_right hx
    simp [this]
  have := Submodule.finrank_sup_add_finrank_inf_eq (D ∙ x) U₁
  rw [hsup, hinf, finrank_bot, add_zero, finrank_span_singleton hx0] at this
  omega

/-! ### Witt's extension theorem (GKT Theorem B.17) -/

section WittTheorem

variable [FiniteDimensional D V] [NeZero (2 : D)]

variable (h) in
/-- The measure `dim U + 2 dim (U ∩ U^⊥)` of Scharlau's induction. -/
private def wittMeasure (U : Submodule D V) : ℕ :=
  finrank D U + 2 * finrank D (U ⊓ h.orthogonal U : Submodule D V)

/-- The step of Witt's theorem for a subspace containing an anisotropic vector `x`. -/
private theorem witt_step_anisotropic (hh : h.Nondegenerate) {U : Submodule D V}
    {x : V} (hxU : x ∈ U) (hx : h x x ≠ 0) (σ : U →ₗ[D] V)
    (hσh : ∀ a b : U, h (σ a) (σ b) = h a b)
    (ih : ∀ (U₁ : Submodule D V), wittMeasure h U₁ < wittMeasure h U → ∀ σ₁ : U₁ →ₗ[D] V,
      Function.Injective σ₁ → (∀ a b : U₁, h (σ₁ a) (σ₁ b) = h a b) →
      ∃ g : h.isometryGroup, ∀ a : U₁, (g : V ≃ₗ[D] V) a = σ₁ a)
    (hσ : Function.Injective σ) :
    ∃ g : h.isometryGroup, ∀ u : U, (g : V ≃ₗ[D] V) u = σ u := by
  set U₁ := U ⊓ h.orthogonal (D ∙ x)
  have hU₁U : U₁ ≤ U := inf_le_left
  set l : V → D := fun v => h v x * (h x x)⁻¹
  have hl : ∀ v, v - l v • x ∈ h.orthogonal (D ∙ x) := fun v => by
    rw [mem_orthogonal_span_singleton, h.map_sub_left, h.map_smul_left, mul_assoc,
      inv_mul_cancel₀ hx, mul_one, sub_self]
  have hdecomp : ∀ u ∈ U, u - l u • x ∈ U₁ := fun u hu =>
    ⟨U.sub_mem hu (U.smul_mem _ hxU), hl u⟩
  have hx0 : x ≠ 0 := fun e => hx (by rw [e, map_zero_left])
  have hdim : finrank D U₁ + 1 = finrank D U :=
    finrank_inf_orthogonal_span_singleton_add_one hxU hx
  have hrad : U₁ ⊓ h.orthogonal U₁ = U ⊓ h.orthogonal U := by
    ext r
    constructor
    · rintro ⟨⟨hrU, hrx⟩, hr⟩
      refine ⟨hrU, fun u hu => ?_⟩
      have : h r u = h r (l u • x) + h r (u - l u • x) := by
        rw [← h.map_add_right, add_sub_cancel]
      rw [this, h.map_smul_right, mem_orthogonal_span_singleton.1 hrx, zero_mul, zero_add]
      exact hr _ (hdecomp u hu)
    · rintro ⟨hrU, hr⟩
      exact ⟨⟨hrU, mem_orthogonal_span_singleton.2 (hr x hxU)⟩, fun u hu => hr u hu.1⟩
  have hlt : wittMeasure h U₁ < wittMeasure h U := by
    unfold wittMeasure; rw [hrad]; omega
  set σ₁ : U₁ →ₗ[D] V := σ.comp (Submodule.inclusion hU₁U)
  obtain ⟨g₁, hg₁⟩ := ih U₁ hlt σ₁ (hσ.comp (Submodule.inclusion_injective hU₁U))
    (fun a b => hσh _ _)
  set xU : U := ⟨x, hxU⟩
  set y := ((g₁⁻¹ : h.isometryGroup) : V ≃ₗ[D] V) (σ xU)
  have hyy : h y y = h x x := by
    simp only [y, isometryGroup_apply, hσh]; rfl
  obtain ⟨g₂, hg₂x, hg₂w⟩ := exists_isometry_map_of_apply_self_eq hh hyy.symm hx
  have hg₁inv : ∀ a : U₁, ((g₁⁻¹ : h.isometryGroup) : V ≃ₗ[D] V) (σ (Submodule.inclusion hU₁U a))
      = a := fun a => by
    rw [← show σ₁ a = σ (Submodule.inclusion hU₁U a) from rfl, ← hg₁ a,
      isometryGroup_coe_inv_apply']
  refine ⟨g₁ * g₂, fun u => ?_⟩
  set u₁ : U₁ := ⟨(u : V) - l u • x, hdecomp u u.2⟩
  have hu : u = l u • xU + Submodule.inclusion hU₁U u₁ := by
    apply Subtype.ext
    simp [u₁, xU]
  have hu₁y : h (u₁ : V) y = 0 := by
    rw [← hg₁inv u₁]
    simp only [y, isometryGroup_apply, hσh]
    exact (hdecomp u u.2).2 x (Submodule.mem_span_singleton_self x)
  have hg₂u₁ : (g₂ : V ≃ₗ[D] V) u₁ = u₁ :=
    hg₂w _ (mem_orthogonal_span_singleton.1 (hdecomp u u.2).2) hu₁y
  have e1 : (g₂ : V ≃ₗ[D] V) (u : V) = l u • y + (u₁ : V) := by
    conv_lhs => rw [show (u : V) = l u • x + (u₁ : V) by simp [u₁]]
    rw [map_add, map_smul, hg₂x, hg₂u₁]
  have e2 : σ u = l u • σ xU + σ₁ u₁ := by
    conv_lhs => rw [hu]
    rw [map_add, map_smul]; rfl
  rw [isometryGroup_coe_mul_apply, e1, map_add, map_smul, hg₁ u₁, e2]
  simp only [y, isometryGroup_coe_inv_apply]

/-- The step of Witt's theorem for a subspace on which the form is alternating and non-zero. -/
private theorem witt_step_alternating (hh : h.Nondegenerate) {U : Submodule D V}
    (hall : ∀ x ∈ U, h x x = 0) {x y₀ : V} (hxU : x ∈ U) (hyU : y₀ ∈ U) (hxy : h x y₀ ≠ 0)
    (σ : U →ₗ[D] V) (hσh : ∀ a b : U, h (σ a) (σ b) = h a b)
    (ih : ∀ (U₁ : Submodule D V), wittMeasure h U₁ < wittMeasure h U → ∀ σ₁ : U₁ →ₗ[D] V,
      Function.Injective σ₁ → (∀ a b : U₁, h (σ₁ a) (σ₁ b) = h a b) →
      ∃ g : h.isometryGroup, ∀ a : U₁, (g : V ≃ₗ[D] V) a = σ₁ a)
    (hσ : Function.Injective σ) :
    ∃ g : h.isometryGroup, ∀ u : U, (g : V ≃ₗ[D] V) u = σ u := by
  have hAlt := isAlternatingCase_of_apply_self hall hxU hyU hxy
  have hswap := hAlt.apply_swap (h := h)
  set y := conj τ (h x y₀)⁻¹ • y₀
  have hyU' : y ∈ U := U.smul_mem _ hyU
  have hp : h.IsHyperbolicPair x y :=
    ⟨hall x hxU, hall y hyU', by rw [h.map_smul_right, conj_conj, mul_inv_cancel₀ hxy]⟩
  have hyx : h y x = -1 := by rw [hswap, hp.2.2]
  set U₁ := U ⊓ h.orthogonal (D ∙ x) ⊓ h.orthogonal (D ∙ y)
  have hU₁U : U₁ ≤ U := inf_le_left.trans inf_le_left
  set a : V → D := fun v => h v y
  set b : V → D := fun v => -h v x
  set p : V → V := fun v => v - a v • x - b v • y
  have hpx : ∀ v, h (p v) x = 0 := fun v => by
    simp only [p, a, b, h.map_sub_left, h.map_smul_left, hp.1, hyx]; noncomm_ring
  have hpy : ∀ v, h (p v) y = 0 := fun v => by
    simp only [p, a, b, h.map_sub_left, h.map_smul_left, hp.2.1, hp.2.2]; noncomm_ring
  have hdecomp : ∀ u ∈ U, p u ∈ U₁ := fun u hu =>
    ⟨⟨U.sub_mem (U.sub_mem hu (U.smul_mem _ hxU)) (U.smul_mem _ hyU'),
      mem_orthogonal_span_singleton.2 (hpx u)⟩, mem_orthogonal_span_singleton.2 (hpy u)⟩
  have hx0 : x ≠ 0 := fun e => by
    have := hp.2.2; rw [e, map_zero_left] at this; exact zero_ne_one this
  have hy0 : y ≠ 0 := fun e => by
    have := hp.2.2; rw [e, map_zero_right] at this; exact zero_ne_one this
  have hdim : finrank D U₁ + 2 = finrank D U := by
    set P := (D ∙ x) ⊔ (D ∙ y)
    have hPU : P ≤ U := sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 hxU)
      ((Submodule.span_singleton_le_iff_mem _ _).2 hyU')
    have hP : finrank D P = 2 := by
      have hxy0 : (D ∙ x) ⊓ (D ∙ y) = ⊥ := by
        rw [eq_bot_iff]
        rintro v ⟨hv, hv'⟩
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
        obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.1 hv'
        have := congrArg (fun w => h w y) hd
        simp only [h.map_smul_left, hp.2.1, hp.2.2, mul_zero, mul_one] at this
        simp [← this]
      have := Submodule.finrank_sup_add_finrank_inf_eq (D ∙ x) (D ∙ y)
      rw [hxy0, finrank_bot, add_zero, finrank_span_singleton hx0,
        finrank_span_singleton hy0] at this
      exact this
    have hsup : P ⊔ U₁ = U := le_antisymm (sup_le hPU hU₁U) (fun u hu => by
      have h1 : a u • x + b u • y ∈ P :=
        Submodule.add_mem_sup (Submodule.mem_span_singleton.2 ⟨a u, rfl⟩ : a u • x ∈ D ∙ x)
          (Submodule.mem_span_singleton.2 ⟨b u, rfl⟩ : b u • y ∈ D ∙ y)
      have := Submodule.add_mem_sup h1 (hdecomp u hu)
      rwa [show a u • x + b u • y + p u = u by simp only [p]; abel] at this)
    have hinf : P ⊓ U₁ = ⊥ := by
      rw [eq_bot_iff]
      intro v hv'
      rw [Submodule.mem_inf] at hv'
      obtain ⟨hv, hv2⟩ := hv'
      have hvx : h v x = 0 := mem_orthogonal_span_singleton.1 hv2.1.2
      have hvy : h v y = 0 := mem_orthogonal_span_singleton.1 hv2.2
      obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Submodule.mem_sup.1 hv
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv₁
      obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 hv₂
      simp only [h.map_add_left, h.map_smul_left, hp.1, hp.2.1, hp.2.2, hyx, mul_zero,
        mul_one, zero_add, add_zero, mul_neg] at hvx hvy
      rw [hvy, neg_eq_zero.1 hvx, zero_smul, zero_smul, add_zero]
      exact Submodule.zero_mem _
    have := Submodule.finrank_sup_add_finrank_inf_eq P U₁
    rw [hsup, hinf, finrank_bot, add_zero, hP] at this
    omega
  have hrad : U₁ ⊓ h.orthogonal U₁ = U ⊓ h.orthogonal U := by
    ext r
    constructor
    · rintro ⟨⟨⟨hrU, hrx⟩, hry⟩, hr⟩
      refine ⟨hrU, fun u hu => ?_⟩
      have : h r u = h r (a u • x) + h r (b u • y) + h r (p u) := by
        rw [← h.map_add_right, ← h.map_add_right]; simp only [p]; abel_nf
      rw [this, h.map_smul_right, h.map_smul_right, mem_orthogonal_span_singleton.1 hrx,
        mem_orthogonal_span_singleton.1 hry, zero_mul, zero_mul, zero_add, zero_add]
      exact hr _ (hdecomp u hu)
    · rintro ⟨hrU, hr⟩
      exact ⟨⟨⟨hrU, mem_orthogonal_span_singleton.2 (hr x hxU)⟩,
        mem_orthogonal_span_singleton.2 (hr y hyU')⟩, fun u hu => hr u (hU₁U hu)⟩
  have hlt : wittMeasure h U₁ < wittMeasure h U := by
    unfold wittMeasure; rw [hrad]; omega
  set σ₁ : U₁ →ₗ[D] V := σ.comp (Submodule.inclusion hU₁U)
  obtain ⟨g₁, hg₁⟩ := ih U₁ hlt σ₁ (hσ.comp (Submodule.inclusion_injective hU₁U))
    (fun a b => hσh _ _)
  set xU : U := ⟨x, hxU⟩
  set yU : U := ⟨y, hyU'⟩
  set gi := ((g₁⁻¹ : h.isometryGroup) : V ≃ₗ[D] V)
  set x' := gi (σ xU)
  set y' := gi (σ yU)
  have hσ' : ∀ c d : U, h (gi (σ c)) (gi (σ d)) = h c d := fun c d => by
    simp only [gi, isometryGroup_apply, hσh]
  have hp' : h.IsHyperbolicPair x' y' := ⟨(hσ' xU xU).trans hp.1, (hσ' yU yU).trans hp.2.1,
    (hσ' xU yU).trans hp.2.2⟩
  obtain ⟨g₂, hg₂x, hg₂y, hg₂w⟩ := exists_isometry_map_isHyperbolicPair hh hAlt hp hp'
  have hg₁inv : ∀ c : U₁, gi (σ (Submodule.inclusion hU₁U c)) = c := fun c => by
    rw [← show σ₁ c = σ (Submodule.inclusion hU₁U c) from rfl, ← hg₁ c]
    exact isometryGroup_coe_inv_apply' g₁ _
  refine ⟨g₁ * g₂, fun u => ?_⟩
  set u₁ : U₁ := ⟨p u, hdecomp u u.2⟩
  have hu : u = a u • xU + b u • yU + Submodule.inclusion hU₁U u₁ := by
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_inclusion, u₁, xU, yU, p]
    abel
  have hu₁x : h (u₁ : V) x = 0 := hpx u
  have hu₁y : h (u₁ : V) y = 0 := hpy u
  have hu₁x' : h (u₁ : V) x' = 0 := by
    rw [← hg₁inv u₁, hσ']; exact hu₁x
  have hu₁y' : h (u₁ : V) y' = 0 := by
    rw [← hg₁inv u₁, hσ']; exact hu₁y
  have hg₂u₁ : (g₂ : V ≃ₗ[D] V) u₁ = u₁ := hg₂w _ hu₁x hu₁y hu₁x' hu₁y'
  have e1 : (g₂ : V ≃ₗ[D] V) (u : V) = a u • x' + b u • y' + (u₁ : V) := by
    conv_lhs => rw [show (u : V) = a u • x + b u • y + (u₁ : V) by simp only [u₁, p]; abel]
    rw [map_add, map_add, map_smul, map_smul, hg₂x, hg₂y, hg₂u₁]
  have e2 : σ u = a u • σ xU + b u • σ yU + σ₁ u₁ := by
    conv_lhs => rw [hu]
    rw [map_add, map_add, map_smul, map_smul]; rfl
  rw [isometryGroup_coe_mul_apply, e1, map_add, map_add, map_smul, map_smul, hg₁ u₁, e2]
  simp only [x', y', gi, isometryGroup_coe_inv_apply]

/-- **Witt's theorem** (GKT Theorem B.17): an injective linear map `σ` from a subspace `U` of a
non-degenerate finite-dimensional `ε`-Hermitian space into the space, preserving the form, extends
to an isometry of the space (`U` need not be non-degenerate; `2` is invertible in `D`). -/
theorem exists_isometry_extend_of_injective (hh : h.Nondegenerate) (U : Submodule D V)
    (σ : U →ₗ[D] V) (hσ : Function.Injective σ) (hσh : ∀ x y : U, h (σ x) (σ y) = h x y) :
    ∃ g : h.isometryGroup, ∀ x : U, (g : V ≃ₗ[D] V) x = σ x := by
  suffices H : ∀ n, ∀ U : Submodule D V, wittMeasure h U = n → ∀ σ : U →ₗ[D] V,
      Function.Injective σ → (∀ x y : U, h (σ x) (σ y) = h x y) →
      ∃ g : h.isometryGroup, ∀ x : U, (g : V ≃ₗ[D] V) x = σ x from H _ U rfl σ hσ hσh
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro U hn σ hσ hσh
  have ih' : ∀ (U₁ : Submodule D V), wittMeasure h U₁ < wittMeasure h U → ∀ σ₁ : U₁ →ₗ[D] V,
      Function.Injective σ₁ → (∀ a b : U₁, h (σ₁ a) (σ₁ b) = h a b) →
      ∃ g : h.isometryGroup, ∀ a : U₁, (g : V ≃ₗ[D] V) a = σ₁ a :=
    fun U₁ hlt σ₁ => ih _ (hn ▸ hlt) U₁ rfl σ₁
  by_cases hU : U = ⊥
  · refine ⟨1, fun x => ?_⟩
    have hx : x = 0 := Subtype.ext ((Submodule.eq_bot_iff U).1 hU (x : V) x.2)
    rw [hx, map_zero, Submodule.coe_zero, map_zero]
  by_cases hA : ∃ x ∈ U, h x x ≠ 0
  · obtain ⟨x, hxU, hx⟩ := hA
    exact witt_step_anisotropic hh hxU hx σ hσh ih' hσ
  push Not at hA
  by_cases hC : ∃ x ∈ U, ∃ y ∈ U, h x y ≠ 0
  · obtain ⟨x, hxU, y, hyU, hxy⟩ := hC
    exact witt_step_alternating hh hA hxU hyU hxy σ hσh ih' hσ
  push Not at hC
  -- `U` is totally isotropic: pass to `U ⊕ U'` with a dual partner `U'`
  have hUiso : h.IsTotallyIsotropic U := hC
  obtain ⟨U', hU'iso, hU'dim, hU'c⟩ := exists_isTotallyIsotropic_isCompl hh hUiso
  set S := LinearMap.range σ
  have hSiso : h.IsTotallyIsotropic S := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [hσh]; exact hC a a.2 b b.2
  obtain ⟨S', hS'iso, hS'dim, hS'c⟩ := exists_isTotallyIsotropic_isCompl hh hSiso
  have hSdim : finrank D S = finrank D U := LinearMap.finrank_range_of_inj hσ
  set σS : U ≃ₗ[D] S := LinearEquiv.ofInjective σ hσ
  have hdS : Disjoint S' (h.orthogonal S) := hS'c.disjoint.symm
  have hrep : ∀ u' : U', ∃ s' ∈ S', ∀ u : U, h (σ u) s' = h u u' := fun u' => by
    obtain ⟨s', hs', hs'f⟩ := exists_mem_forall_apply_eq hdS (by rw [hS'dim])
      ((h.flipApply (u' : V)).comp (U.subtype.comp σS.symm.toLinearMap))
    refine ⟨s', hs', fun u => ?_⟩
    have := hs'f (σS u)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, Submodule.coe_subtype, flipApply_apply] at this
    rwa [LinearEquiv.ofInjective_apply] at this
  choose r hrS' hr using hrep
  have runiq : ∀ (u' : U') (v : V), v ∈ S' → (∀ u : U, h (σ u) v = h u u') → v = r u' :=
    fun u' v hv H => eq_of_forall_apply_eq hdS hv (hrS' u') fun s hs => by
      obtain ⟨u, rfl⟩ := hs
      rw [H u, hr u' u]
  set rL : U' →ₗ[D] V :=
    { toFun := r
      map_add' := fun c d => (runiq _ _ (S'.add_mem (hrS' c) (hrS' d)) fun u => by
        rw [h.map_add_right, hr, hr, Submodule.coe_add, h.map_add_right]).symm
      map_smul' := fun c d => (runiq _ _ (S'.smul_mem c (hrS' d)) fun u => by
        rw [h.map_smul_right, hr, Submodule.coe_smul, h.map_smul_right]).symm }
  set Ut := U ⊔ U'
  have hUU' : Disjoint U U' := disjoint_of_isCompl_orthogonal hUiso hU'c
  set P := U.comap Ut.subtype
  set Q := U'.comap Ut.subtype
  have hPQ : IsCompl P Q := by
    constructor
    · rw [Submodule.disjoint_def]
      intro z hzP hzQ
      exact Subtype.ext (Submodule.disjoint_def.1 hUU' _ hzP hzQ)
    · rw [codisjoint_iff, eq_top_iff]
      intro z _
      obtain ⟨u, hu, u', hu', huu'⟩ := Submodule.mem_sup.1 z.2
      have : z = ⟨u, Submodule.mem_sup_left hu⟩ + ⟨u', Submodule.mem_sup_right hu'⟩ :=
        Subtype.ext huu'.symm
      rw [this]
      exact Submodule.add_mem_sup hu hu'
  set σt : Ut →ₗ[D] V := LinearMap.ofIsCompl hPQ
    (σ.comp (Submodule.comapSubtypeEquivOfLe (le_sup_left : U ≤ Ut)).toLinearMap)
    (rL.comp (Submodule.comapSubtypeEquivOfLe (le_sup_right : U' ≤ Ut)).toLinearMap)
  have hσtU : ∀ u : U, σt ⟨u, Submodule.mem_sup_left u.2⟩ = σ u := fun u => by
    have := LinearMap.ofIsCompl_apply_left hPQ
      (φ := σ.comp (Submodule.comapSubtypeEquivOfLe (le_sup_left : U ≤ Ut)).toLinearMap)
      (ψ := rL.comp (Submodule.comapSubtypeEquivOfLe (le_sup_right : U' ≤ Ut)).toLinearMap)
      ⟨⟨u, Submodule.mem_sup_left u.2⟩, u.2⟩
    exact this
  have hσtU' : ∀ u' : U', σt ⟨u', Submodule.mem_sup_right u'.2⟩ = r u' := fun u' => by
    have := LinearMap.ofIsCompl_apply_right hPQ
      (φ := σ.comp (Submodule.comapSubtypeEquivOfLe (le_sup_left : U ≤ Ut)).toLinearMap)
      (ψ := rL.comp (Submodule.comapSubtypeEquivOfLe (le_sup_right : U' ≤ Ut)).toLinearMap)
      ⟨⟨u', Submodule.mem_sup_right u'.2⟩, u'.2⟩
    exact this
  have hdec : ∀ z : Ut, ∃ u : U, ∃ u' : U',
      z = ⟨u, Submodule.mem_sup_left u.2⟩ + ⟨u', Submodule.mem_sup_right u'.2⟩ := fun z => by
    obtain ⟨u, hu, u', hu', huu'⟩ := Submodule.mem_sup.1 z.2
    exact ⟨⟨u, hu⟩, ⟨u', hu'⟩, Subtype.ext huu'.symm⟩
  have hσth : ∀ z₁ z₂ : Ut, h (σt z₁) (σt z₂) = h z₁ z₂ := by
    intro z₁ z₂
    obtain ⟨u₁, u₁', rfl⟩ := hdec z₁
    obtain ⟨u₂, u₂', rfl⟩ := hdec z₂
    simp only [map_add, hσtU, hσtU', Submodule.coe_add, h.map_add_left, h.map_add_right]
    rw [hσh, hr, hS'iso _ (hrS' u₁') _ (hrS' u₂'), hC _ u₁.2 _ u₂.2,
      hU'iso _ u₁'.2 _ u₂'.2]
    rw [h.conj_swap (σ u₂) (r u₁'), hr, ← h.conj_swap]
  have hnd : (h.restrict Ut).Nondegenerate := restrict_sup_nondegenerate hh hUiso hU'c
  have hσtinj : Function.Injective σt := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro z hz
    rw [LinearMap.mem_ker] at hz
    refine (Submodule.mem_bot D).2 (hnd z fun w => ?_)
    rw [restrict_apply, ← hσth, hz, map_zero_left]
  have hlt : wittMeasure h Ut < wittMeasure h U := by
    unfold wittMeasure
    have hrad0 : Ut ⊓ h.orthogonal Ut = ⊥ := restrict_nondegenerate_iff.1 hnd
    have hradU : U ⊓ h.orthogonal U = U :=
      inf_eq_left.2 (isTotallyIsotropic_iff_le_orthogonal.1 hUiso)
    have hdimUt : finrank D Ut = finrank D U + finrank D U' := by
      have := Submodule.finrank_sup_add_finrank_inf_eq U U'
      rw [disjoint_iff.1 hUU', finrank_bot, add_zero] at this
      exact this
    have hpos : 0 < finrank D U :=
      Nat.pos_of_ne_zero fun e => hU (Submodule.finrank_eq_zero.1 e)
    rw [hrad0, hradU, finrank_bot, hdimUt, hU'dim]
    omega
  obtain ⟨g, hg⟩ := ih' Ut hlt σt hσtinj hσth
  exact ⟨g, fun u => (hg ⟨u, Submodule.mem_sup_left u.2⟩).trans (hσtU u)⟩

end WittTheorem

/-! ### Consequences: cancellation, the Witt index, the Witt decomposition, diagonalization -/

section Consequences

variable [FiniteDimensional D V] [NeZero (2 : D)]

/-- Witt cancellation in the form of Scharlau 7.9.2 (i): an isometry between two subspaces is the
restriction of an isometry `g` of the space, which then maps the orthogonal of the first onto the
orthogonal of the second. -/
theorem exists_isometry_of_isometryEquiv (hh : h.Nondegenerate) {U U' : Submodule D V}
    (φ : IsometryEquiv (h.restrict U) (h.restrict U')) :
    ∃ g : h.isometryGroup, (∀ u : U, (g : V ≃ₗ[D] V) u = φ u) ∧
      U.map (g : V ≃ₗ[D] V).toLinearMap = U' ∧
      (h.orthogonal U).map (g : V ≃ₗ[D] V).toLinearMap = h.orthogonal U' := by
  set σ : U →ₗ[D] V := U'.subtype.comp φ.toLinearEquiv.toLinearMap
  have hσ : Function.Injective σ :=
    (Submodule.injective_subtype U').comp φ.toLinearEquiv.injective
  have hσh : ∀ a b : U, h (σ a) (σ b) = h a b := fun a b => φ.map_app a b
  obtain ⟨g, hg⟩ := exists_isometry_extend_of_injective hh U σ hσ hσh
  have hmap : U.map (g : V ≃ₗ[D] V).toLinearMap = U' := by
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      rw [LinearEquiv.coe_coe, hg ⟨u, hu⟩]; exact (φ ⟨u, hu⟩).2
    · intro u' hu'
      refine ⟨(φ.symm ⟨u', hu'⟩ : U), (φ.symm ⟨u', hu'⟩).2, ?_⟩
      rw [LinearEquiv.coe_coe, hg]
      change ((φ (φ.symm ⟨u', hu'⟩) : U') : V) = u'
      rw [IsometryEquiv.apply_symm_apply]
  exact ⟨g, hg, hmap, by rw [map_orthogonal, hmap]⟩

/-- Witt cancellation: isometric subspaces of a non-degenerate space have isometric orthogonal
complements (GKT Theorem B.11, uniqueness; Scharlau 7.9.2 (i)). -/
theorem nonempty_isometryEquiv_orthogonal (hh : h.Nondegenerate) {U U' : Submodule D V}
    (φ : IsometryEquiv (h.restrict U) (h.restrict U')) :
    Nonempty (IsometryEquiv (h.restrict (h.orthogonal U)) (h.restrict (h.orthogonal U'))) := by
  obtain ⟨g, -, -, hg⟩ := exists_isometry_of_isometryEquiv hh φ
  exact ⟨{ toLinearEquiv := ((g : V ≃ₗ[D] V).submoduleMap (h.orthogonal U)).trans
              (LinearEquiv.ofEq _ _ hg),
            map_app' := fun a b => isometryGroup_apply g a b }⟩

variable (h) in
/-- The Witt index: the largest dimension of a totally isotropic subspace (GKT Definition B.12). -/
def wittIndex : ℕ := sSup {r | ∃ U : Submodule D V, h.IsTotallyIsotropic U ∧ finrank D U = r}

omit [NeZero (2 : D)] in
private theorem bddAbove_wittIndex :
    BddAbove {r | ∃ U : Submodule D V, h.IsTotallyIsotropic U ∧ finrank D U = r} :=
  ⟨finrank D V, by rintro _ ⟨U, -, rfl⟩; exact Submodule.finrank_le U⟩

omit [NeZero (2 : D)] in
theorem finrank_le_wittIndex {U : Submodule D V} (hU : h.IsTotallyIsotropic U) :
    finrank D U ≤ h.wittIndex :=
  le_csSup bddAbove_wittIndex ⟨U, hU, rfl⟩

omit [NeZero (2 : D)] in
theorem exists_isTotallyIsotropic_finrank_eq_wittIndex :
    ∃ U : Submodule D V, h.IsTotallyIsotropic U ∧ finrank D U = h.wittIndex :=
  Nat.sSup_mem (⟨0, ⊥, isTotallyIsotropic_bot, finrank_bot D V⟩ :
    Set.Nonempty {r | ∃ U : Submodule D V, h.IsTotallyIsotropic U ∧ finrank D U = r})
    bddAbove_wittIndex

omit [NeZero (2 : D)] in
/-- A subspace has subspaces of every smaller dimension. -/
private theorem exists_le_finrank_eq {X : Submodule D V} {m : ℕ} (hm : m ≤ finrank D X) :
    ∃ X₁ ≤ X, finrank D X₁ = m := by
  set b := Module.finBasis D X
  set v : Fin m → V := fun i => (b (Fin.castLE hm i) : V)
  have hli : LinearIndependent D v :=
    (b.linearIndependent.comp _ (Fin.castLE_injective hm)).map' X.subtype (Submodule.ker_subtype X)
  refine ⟨Submodule.span D (Set.range v), ?_, by rw [finrank_span_eq_card hli, Fintype.card_fin]⟩
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact (b (Fin.castLE hm i)).2

/-- All maximal totally isotropic subspaces have the dimension `wittIndex` (Scharlau 7.9.2 (ii)). -/
theorem finrank_eq_wittIndex_of_maximal (hh : h.Nondegenerate) {X : Submodule D V}
    (hX : h.IsTotallyIsotropic X) (hmax : ∀ X', h.IsTotallyIsotropic X' → X ≤ X' → X' = X) :
    finrank D X = h.wittIndex := by
  obtain ⟨X₀, hX₀, hd⟩ := exists_isTotallyIsotropic_finrank_eq_wittIndex (h := h)
  obtain ⟨X₁, hX₁, hd₁⟩ := exists_le_finrank_eq (X := X₀) (m := finrank D X)
    (hd ▸ finrank_le_wittIndex hX)
  set e : X ≃ₗ[D] X₁ := LinearEquiv.ofFinrankEq _ _ hd₁.symm
  set σ : X →ₗ[D] V := X₁.subtype.comp e.toLinearMap
  obtain ⟨g, hg⟩ := exists_isometry_extend_of_injective hh X σ
    ((Submodule.injective_subtype X₁).comp e.injective)
    (fun a b => by
      change h ((e a : X₁) : V) ((e b : X₁) : V) = h a b
      rw [hX₀ _ (hX₁ (e a).2) _ (hX₁ (e b).2), hX _ a.2 _ b.2])
  set Y := X₀.map ((g⁻¹ : h.isometryGroup) : V ≃ₗ[D] V).toLinearMap
  have hY : h.IsTotallyIsotropic Y := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [LinearEquiv.coe_coe, isometryGroup_apply]
    exact hX₀ a ha b hb
  have hXY : X ≤ Y := fun x hx => ⟨(g : V ≃ₗ[D] V) x, by rw [hg ⟨x, hx⟩]; exact hX₁ (e _).2,
    by rw [LinearEquiv.coe_coe, isometryGroup_coe_inv_apply']⟩
  have := hmax Y hY hXY
  rw [← hd, ← this]
  exact LinearEquiv.finrank_map_eq _ X₀

omit [FiniteDimensional D V] [NeZero (2 : D)] in
/-- In a decomposition `V = (X ⊕ X') ⊥ V_a` with `V_a` anisotropic, `X` is maximal totally
isotropic. -/
private theorem maximal_of_anisotropic {X X' : Submodule D V} (hX : h.IsTotallyIsotropic X)
    (hc : IsCompl (h.orthogonal X) X')
    (hc' : IsCompl (X ⊔ X') (h.orthogonal (X ⊔ X')))
    (ha : (h.restrict (h.orthogonal (X ⊔ X'))).Anisotropic) :
    ∀ U, h.IsTotallyIsotropic U → X ≤ U → U = X := by
  intro U hU hXU
  refine le_antisymm (fun u hu => ?_) hXU
  have hmem : u ∈ (X ⊔ X') ⊔ h.orthogonal (X ⊔ X') := by rw [hc'.sup_eq_top]; trivial
  obtain ⟨w, hw, a, ha', rfl⟩ := Submodule.mem_sup.1 hmem
  obtain ⟨x, hx, x', hx', rfl⟩ := Submodule.mem_sup.1 hw
  -- `x' ⊥ X`, hence `x' = 0`
  have hx'X : x' ∈ h.orthogonal X := fun y hy => by
    have e1 := hU (x + x' + a) hu y (hXU hy)
    rw [h.map_add_left, h.map_add_left, hX x hx y hy, zero_add,
      (ha' y (Submodule.mem_sup_left hy)), add_zero] at e1
    exact e1
  have hx'0 : x' = 0 := Submodule.disjoint_def.1 hc.disjoint _ hx'X hx'
  subst hx'0
  rw [add_zero] at hu ⊢
  -- `a = u - x ∈ U` is isotropic, hence `0`
  have haU : a ∈ U := by
    have := U.sub_mem hu (hXU hx); rwa [add_sub_cancel_left] at this
  have ha0 : a = 0 := by
    have := ha ⟨a, ha'⟩ (hU a haU a haU)
    exact congrArg Subtype.val this
  rw [ha0, add_zero]; exact hx

/-- GKT Theorem B.11 (existence): `V = (X ⊕ X*) ⊥ V_a` with `X`, `X*` totally isotropic of dimension
the Witt index, `X ⊕ X*` hyperbolic (`V = X^⊥ ⊕ X*`) and `V_a = (X ⊕ X*)^⊥` anisotropic. -/
theorem exists_wittDecomposition (hh : h.Nondegenerate) :
    ∃ X X' : Submodule D V, h.IsTotallyIsotropic X ∧ h.IsTotallyIsotropic X' ∧
      IsCompl (h.orthogonal X) X' ∧ IsCompl (X ⊔ X') (h.orthogonal (X ⊔ X')) ∧
      (h.restrict (h.orthogonal (X ⊔ X'))).Anisotropic ∧ finrank D X = h.wittIndex ∧
      finrank D X' = h.wittIndex := by
  obtain ⟨X, hX, hd⟩ := exists_isTotallyIsotropic_finrank_eq_wittIndex (h := h)
  have hmax : ∀ U, h.IsTotallyIsotropic U → X ≤ U → U = X := fun U hU hXU =>
    (Submodule.eq_of_le_of_finrank_eq hXU (le_antisymm (Submodule.finrank_mono hXU)
      (hd ▸ finrank_le_wittIndex hU))).symm
  obtain ⟨X', hX', hd', hc⟩ := exists_isTotallyIsotropic_isCompl hh hX
  have hnd := restrict_sup_nondegenerate hh hX hc
  have hc' := isCompl_orthogonal_of_restrict_nondegenerate hh hnd
  refine ⟨X, X', hX, hX', hc, hc', fun a ha => ?_, hd, hd' ▸ hd⟩
  -- an isotropic `a ∈ (X ⊕ X')^⊥` extends `X`
  by_contra ha0
  have haX : (a : V) ∉ X := fun H => ha0 (Subtype.ext (Submodule.disjoint_def.1 hc'.disjoint _
    (Submodule.mem_sup_left H) a.2))
  have hiso : h.IsTotallyIsotropic (X ⊔ D ∙ (a : V)) := by
    intro u hu v hv
    obtain ⟨x₁, hx₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.1 hu
    obtain ⟨y₁, hy₁, v₂, hv₂, rfl⟩ := Submodule.mem_sup.1 hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hu₂
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 hv₂
    have h1 : h x₁ a = 0 := (h.apply_eq_zero_comm).1 (a.2 x₁ (Submodule.mem_sup_left hx₁))
    have h2 : h a y₁ = 0 := a.2 y₁ (Submodule.mem_sup_left hy₁)
    have h3 : h a a = 0 := ha
    simp only [h.map_add_left, h.map_add_right, h.map_smul_left, h.map_smul_right,
      hX x₁ hx₁ y₁ hy₁, h1, h2, h3, mul_zero, zero_mul, add_zero]
  have heq := hmax _ hiso le_sup_left
  have hv' : (a : V) ∈ X ⊔ D ∙ (a : V) :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  rw [heq] at hv'
  exact haX hv'

omit [NeZero (2 : D)] in
/-- A hyperbolic space `X ⊕ X'` (with `X`, `X'` totally isotropic and `V = X^⊥ ⊕ X'`) has a standard
basis indexed by `Fin (dim X)`. -/
theorem exists_standardBasis_restrict_sup (hh : h.Nondegenerate) {X X' : Submodule D V}
    (hX : h.IsTotallyIsotropic X) (hX' : h.IsTotallyIsotropic X')
    (hc : IsCompl (h.orthogonal X) X') (hd : finrank D X' = finrank D X) :
    Nonempty ((h.restrict (X ⊔ X')).StandardBasis (Fin (finrank D X))) := by
  have hnd := restrict_sup_nondegenerate hh hX hc
  have hdisj := disjoint_of_isCompl_orthogonal hX hc
  have hH : finrank D (X ⊔ X' : Submodule D V) = 2 * finrank D X := by
    have := Submodule.finrank_sup_add_finrank_inf_eq X X'
    rw [disjoint_iff.1 hdisj, finrank_bot, add_zero, hd] at this
    omega
  have hL : finrank D (X.comap (X ⊔ X').subtype) = finrank D X :=
    (Submodule.comapSubtypeEquivOfLe (le_sup_left : X ≤ X ⊔ X')).finrank_eq
  have hL' : finrank D (X'.comap (X ⊔ X').subtype) = finrank D X :=
    ((Submodule.comapSubtypeEquivOfLe (le_sup_right : X' ≤ X ⊔ X')).finrank_eq).trans hd
  have hLiso : (h.restrict (X ⊔ X')).IsTotallyIsotropic (X.comap (X ⊔ X').subtype) :=
    fun a ha b hb => show h a b = 0 from
      hX (a : V) (by simpa using Submodule.mem_comap.1 ha) (b : V)
        (by simpa using Submodule.mem_comap.1 hb)
  have hL'iso : (h.restrict (X ⊔ X')).IsTotallyIsotropic (X'.comap (X ⊔ X').subtype) :=
    fun a ha b hb => show h a b = 0 from
      hX' (a : V) (by simpa using Submodule.mem_comap.1 ha) (b : V)
        (by simpa using Submodule.mem_comap.1 hb)
  have hLlag := isLagrangian_of_two_mul_finrank hnd hLiso (by rw [hL, hH])
  have hL'lag := isLagrangian_of_two_mul_finrank hnd hL'iso (by rw [hL', hH])
  have hLL' : IsCompl (X.comap (X ⊔ X').subtype) (X'.comap (X ⊔ X').subtype) := by
    rw [hLlag.isCompl_iff_disjoint hnd hL'lag, Submodule.disjoint_def]
    intro z hz hz'
    exact Subtype.ext (Submodule.disjoint_def.1 hdisj _ (by simpa using Submodule.mem_comap.1 hz)
      (by simpa using Submodule.mem_comap.1 hz'))
  obtain ⟨e, -⟩ := exists_standardBasis hnd hLlag hL'lag hLL'
    (Module.finBasisOfFinrankEq D _ hL)
  exact ⟨e⟩

/-- GKT Theorem B.11 (uniqueness): in two Witt decompositions the hyperbolic parts have the same
dimension and the anisotropic parts are isometric. -/
theorem wittDecomposition_unique (hh : h.Nondegenerate) {X₁ X₁' X₂ X₂' : Submodule D V}
    (h₁ : h.IsTotallyIsotropic X₁) (h₁' : h.IsTotallyIsotropic X₁')
    (hc₁ : IsCompl (h.orthogonal X₁) X₁') (hd₁ : finrank D X₁' = finrank D X₁)
    (ha₁ : (h.restrict (h.orthogonal (X₁ ⊔ X₁'))).Anisotropic)
    (h₂ : h.IsTotallyIsotropic X₂) (h₂' : h.IsTotallyIsotropic X₂')
    (hc₂ : IsCompl (h.orthogonal X₂) X₂') (hd₂ : finrank D X₂' = finrank D X₂)
    (ha₂ : (h.restrict (h.orthogonal (X₂ ⊔ X₂'))).Anisotropic) :
    finrank D X₁ = finrank D X₂ ∧ Nonempty (IsometryEquiv (h.restrict (h.orthogonal (X₁ ⊔ X₁')))
      (h.restrict (h.orthogonal (X₂ ⊔ X₂')))) := by
  have hc₁' :=
    isCompl_orthogonal_of_restrict_nondegenerate hh (restrict_sup_nondegenerate hh h₁ hc₁)
  have hc₂' :=
    isCompl_orthogonal_of_restrict_nondegenerate hh (restrict_sup_nondegenerate hh h₂ hc₂)
  have e₁ := finrank_eq_wittIndex_of_maximal hh h₁ (maximal_of_anisotropic h₁ hc₁ hc₁' ha₁)
  have e₂ := finrank_eq_wittIndex_of_maximal hh h₂ (maximal_of_anisotropic h₂ hc₂ hc₂' ha₂)
  have heq : finrank D X₁ = finrank D X₂ := e₁.trans e₂.symm
  refine ⟨heq, ?_⟩
  obtain ⟨b₁⟩ := exists_standardBasis_restrict_sup hh h₁ h₁' hc₁ hd₁
  obtain ⟨b₂⟩ := exists_standardBasis_restrict_sup hh h₂ h₂' hc₂ hd₂
  exact nonempty_isometryEquiv_orthogonal hh (b₁.isometryEquiv (b₂.reindex (finCongr heq.symm)))

end Consequences

/-! ### Diagonalization (GKT Theorem B.15) -/

section Diagonalization

/-- An orthogonal family of anisotropic vectors is linearly independent. -/
theorem linearIndependent_of_orthogonal {ι : Type*} [Fintype ι] {v : ι → V}
    (horth : ∀ i j, i ≠ j → h (v i) (v j) = 0) (hani : ∀ i, h (v i) (v i) ≠ 0) :
    LinearIndependent D v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have := congrArg (fun w => h w (v j)) hc
  simp only [h.map_sum_left, h.map_smul_left, map_zero_left] at this
  rw [Finset.sum_eq_single j (fun i _ hij => by rw [horth i j hij, mul_zero])
    (by simp)] at this
  exact (mul_eq_zero.1 this).resolve_right (hani j)

variable [FiniteDimensional D V] [NeZero (2 : D)]

/-- Outside the alternating case, a non-degenerate subspace has an orthogonal basis of anisotropic
vectors. -/
theorem exists_orthogonal_family (hna : ¬ IsAlternatingCase τ ε) :
    ∀ n, ∀ U : Submodule D V, (h.restrict U).Nondegenerate → finrank D U = n →
      ∃ v : Fin n → V, (∀ i, v i ∈ U) ∧ (∀ i j, i ≠ j → h (v i) (v j) = 0) ∧
        ∀ i, h (v i) (v i) ≠ 0 := by
  intro n
  induction n with
  | zero => intro U _ _; exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    intro U hU hn
    have hU0 : U ≠ ⊥ := fun e => by rw [e, finrank_bot] at hn; omega
    obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    obtain ⟨w, hw⟩ : ∃ w : U, h u w ≠ 0 := by
      by_contra H
      push Not at H
      exact hu0 (congrArg Subtype.val (hU ⟨u, huU⟩ H))
    obtain ⟨x, hxU, hx⟩ : ∃ x ∈ U, h x x ≠ 0 := by
      by_contra H
      push Not at H
      exact hna (isAlternatingCase_of_apply_self H huU w.2 hw)
    have hdim : finrank D (U ⊓ h.orthogonal (D ∙ x) : Submodule D V) = n := by
      have := finrank_inf_orthogonal_span_singleton_add_one (h := h) hxU hx; omega
    set U₁ := U ⊓ h.orthogonal (D ∙ x)
    have hU₁ : (h.restrict U₁).Nondegenerate := by
      intro z hz
      have hzx : h z x = 0 := mem_orthogonal_span_singleton.1 (Submodule.mem_inf.1 z.2).2
      have hall : ∀ y : U, h z y = 0 := fun y => by
        set l := h y x * (h x x)⁻¹
        have hy₁ : (y : V) - l • x ∈ U₁ := Submodule.mem_inf.2 ⟨U.sub_mem y.2 (U.smul_mem _ hxU),
          by rw [mem_orthogonal_span_singleton, h.map_sub_left, h.map_smul_left, mul_assoc,
            inv_mul_cancel₀ hx, mul_one, sub_self]⟩
        have : h z y = h z (l • x) + h z ((y : V) - l • x) := by
          rw [← h.map_add_right, add_sub_cancel]
        rw [this, h.map_smul_right, hzx, zero_mul, zero_add]
        exact hz ⟨_, hy₁⟩
      exact Subtype.ext (congrArg Subtype.val
        (hU ⟨z, (Submodule.mem_inf.1 z.2).1⟩ hall) : (z : V) = 0)
    obtain ⟨v₁, hv₁U, hv₁o, hv₁a⟩ := ih U₁ hU₁ hdim
    have hv₁x : ∀ i, h (v₁ i) x = 0 := fun i =>
      mem_orthogonal_span_singleton.1 (Submodule.mem_inf.1 (hv₁U i)).2
    refine ⟨Fin.cons x v₁, fun i => ?_, fun i j hij => ?_, fun i => ?_⟩
    · refine Fin.cases hxU (fun i => ?_) i
      exact (Submodule.mem_inf.1 (hv₁U i)).1
    · induction i using Fin.cases <;> induction j using Fin.cases
      · exact absurd rfl hij
      · simp only [Fin.cons_zero, Fin.cons_succ]; exact (h.apply_eq_zero_comm).1 (hv₁x _)
      · simp only [Fin.cons_zero, Fin.cons_succ]; exact hv₁x _
      · simp only [Fin.cons_succ]; exact hv₁o _ _ (fun e => hij (by rw [e]))
    · refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hx
      · simpa using hv₁a i

/-- GKT Theorem B.15 (diagonalization): outside the alternating case (`τ` trivial and `ε = -1`), a
non-degenerate `ε`-Hermitian space has an orthogonal basis `b`, so that
`V = ⟨a₁⟩ ⊕ ⋯ ⊕ ⟨aₙ⟩` with `aᵢ = h(bᵢ, bᵢ)`, `aᵢ^τ = ε aᵢ`, `aᵢ ≠ 0`. -/
theorem exists_orthogonal_basis (hna : ¬ IsAlternatingCase τ ε) (hh : h.Nondegenerate) :
    ∃ b : Module.Basis (Fin (finrank D V)) D V,
      (∀ i j, i ≠ j → h (b i) (b j) = 0) ∧ ∀ i, h (b i) (b i) ≠ 0 := by
  have htop : (h.restrict (⊤ : Submodule D V)).Nondegenerate := fun x hx =>
    Subtype.ext (hh x fun y => hx ⟨y, trivial⟩)
  obtain ⟨v, -, hvo, hva⟩ := exists_orthogonal_family hna (finrank D V) ⊤ htop (finrank_top D V)
  refine ⟨basisOfLinearIndependentOfCardEqFinrank' v (linearIndependent_of_orthogonal hvo hva)
    (Fintype.card_fin _), ?_, ?_⟩
  · intro i j hij; simpa using hvo i j hij
  · intro i; simpa using hva i

end Diagonalization

end EpsilonHermitianForm

end Langlands

end
