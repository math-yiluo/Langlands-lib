import Langlands.LinearAlgebra.EpsilonHermitian.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Isotropic vectors and subspaces; hyperbolic pairs; the space `M^⊥/M`

GKT Appendix B.2.1 (Definition B.8, Proposition B.9, Definition B.10) and §4.2 (Lemma 4.10 (a),
Lemma 4.11 (a), Lemma 4.14 for the form).

For an `ε`-Hermitian form `h` on a finite-dimensional left `D`-module `V`:

* a vector `x` is isotropic if `h x x = 0`; a subspace `U` is totally isotropic if `h` vanishes
  on `U × U`, that is `U ≤ U^⊥` (Lemma 4.10 (a));
* `exists_mem_forall_apply_eq`: if `Y ∩ X^⊥ = 0` and `dim Y = dim X`, every linear form on `X`
  is `h(·, y)` for a unique `y ∈ Y`;
* `exists_isTotallyIsotropic_isCompl` (Lemma 4.11 (a)): a totally isotropic `X` in a
  non-degenerate space has a totally isotropic partner `X*` with `V = X^⊥ ⊕ X*`; then `X ⊕ X*`
  is non-degenerate and `X^⊥ = X ⊕ (X ⊕ X*)^⊥`;
* `exists_isHyperbolicPair` (Proposition B.9): a non-zero isotropic vector of a non-degenerate
  space lies in a hyperbolic pair `h x x = h y y = 0`, `h x y = 1`; `2` is invertible in `D`;
* `quotient`: the form induced on `V ⧸ N` for `N` in the radical; `reduction M` is the form on
  `M^⊥/M` for a totally isotropic `M`, non-degenerate when `h` is (Lemma 4.14).
-/

noncomputable section

namespace Langlands

namespace EpsilonHermitianForm

open Module
open Langlands.RingInvo (conj conj_conj)

variable {D : Type*} [DivisionRing D] {τ : _root_.RingInvo D} {ε : ℤˣ}
  {V : Type*} [AddCommGroup V] [Module D V] (h : EpsilonHermitianForm τ ε V)

/-! ### Isotropic vectors and totally isotropic subspaces -/

/-- The form is anisotropic: `h x x = 0` only for `x = 0` (GKT Definition B.8). -/
def Anisotropic : Prop := ∀ x, h x x = 0 → x = 0

/-- A subspace is totally isotropic if the form vanishes on it (GKT Definition B.8). -/
def IsTotallyIsotropic (U : Submodule D V) : Prop := ∀ x ∈ U, ∀ y ∈ U, h x y = 0

variable {h}

/-- `U` is totally isotropic if and only if `U ≤ U^⊥` (GKT Lemma 4.10 (a)). -/
theorem isTotallyIsotropic_iff_le_orthogonal {U : Submodule D V} :
    h.IsTotallyIsotropic U ↔ U ≤ h.orthogonal U :=
  ⟨fun H _ hx y hy => H _ hx y hy, fun H _ hx y hy => H hx y hy⟩

theorem IsTotallyIsotropic.mono {U U' : Submodule D V} (hU' : h.IsTotallyIsotropic U')
    (hle : U ≤ U') : h.IsTotallyIsotropic U :=
  fun x hx y hy => hU' x (hle hx) y (hle hy)

theorem isTotallyIsotropic_bot : h.IsTotallyIsotropic ⊥ := fun _ hx _ _ => by
  rw [(Submodule.mem_bot D).1 hx, map_zero_left]

theorem isTotallyIsotropic_span_singleton {x : V} (hx : h x x = 0) :
    h.IsTotallyIsotropic (D ∙ x) := by
  intro u hu v hv
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hu
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hv
  rw [h.map_smul_left, h.map_smul_right, hx, zero_mul, mul_zero]

theorem IsTotallyIsotropic.restrict_eq_zero {U : Submodule D V} (hU : h.IsTotallyIsotropic U)
    (x y : U) : h.restrict U x y = 0 := hU x x.2 y y.2

/-! ### Representing linear forms -/

/-- If `Y ∩ X^⊥ = 0` and `dim Y = dim X`, every `D`-linear form `f` on `X` is `x ↦ h x y` for some
`y ∈ Y`. -/
theorem exists_mem_forall_apply_eq [FiniteDimensional D V] {X Y : Submodule D V}
    (hd : Disjoint Y (h.orthogonal X)) (hdim : finrank D Y = finrank D X) (f : X →ₗ[D] D) :
    ∃ y ∈ Y, ∀ x : X, h x y = f x := by
  set b := Module.finBasis D X
  set ψ : Y →ₗ[D] (Fin (finrank D X) → D) :=
    LinearMap.pi fun i => (h.flipApply ((b i : X) : V)).comp Y.subtype with hψ
  have hψ_apply : ∀ y i, ψ y i = h y ((b i : X) : V) := fun _ _ => rfl
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro y hy
    rw [LinearMap.mem_ker] at hy
    have hy' : (y : V) ∈ h.orthogonal X := by
      intro u hu
      have hu' : u = ∑ i, b.repr ⟨u, hu⟩ i • ((b i : X) : V) := by
        have := congrArg Subtype.val (b.sum_repr ⟨u, hu⟩)
        rw [Submodule.coe_sum] at this
        simp only [Submodule.coe_smul] at this
        exact this.symm
      rw [hu', h.map_sum_right]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [h.map_smul_right, ← hψ_apply, hy, Pi.zero_apply, zero_mul]
    have := Submodule.disjoint_def.1 hd y y.2 hy'
    exact (Submodule.mem_bot D).2 (Subtype.ext this)
  have hsurj : Function.Surjective ψ := by
    rwa [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    rw [Module.finrank_fin_fun, hdim]
  obtain ⟨y, hy⟩ := hsurj fun i => ((ε : ℤ) : D) * conj τ (f (b i))
  refine ⟨y, y.2, fun x => ?_⟩
  have hx : x = ∑ i, b.repr x i • b i := (b.sum_repr x).symm
  have hyx : h y x = ((ε : ℤ) : D) * conj τ (f x) := by
    conv_lhs => rw [hx]
    rw [Submodule.coe_sum, h.map_sum_right]
    conv_rhs => rw [hx, map_sum, RingInvo.conj_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, h.map_smul_right, ← hψ_apply, hy, map_smul, smul_eq_mul,
      RingInvo.conj_mul, mul_assoc]
  rw [h.conj_swap (y : V) (x : V), hyx, RingInvo.conj_mul, conj_conj, RingInvo.conj_intCast,
    ← mul_assoc, units_int_cast_commute, mul_assoc, units_int_cast_mul_self', mul_one]

/-- The vector `y` of `exists_mem_forall_apply_eq` is unique. -/
theorem eq_of_forall_apply_eq {X Y : Submodule D V} (hd : Disjoint Y (h.orthogonal X))
    {y y' : V} (hy : y ∈ Y) (hy' : y' ∈ Y) (H : ∀ x ∈ X, h x y = h x y') : y = y' := by
  have : y - y' ∈ h.orthogonal X := mem_orthogonal'.2 fun x hx => by
    rw [h.map_sub_right, H x hx, sub_self]
  exact sub_eq_zero.1 (Submodule.disjoint_def.1 hd _ (Y.sub_mem hy hy') this)

/-- Under the hypotheses of `exists_mem_forall_apply_eq`, a basis of `X` has a dual family in `Y`:
`h (b i) (c j) = δᵢⱼ`. -/
theorem exists_dual_family [FiniteDimensional D V] {X Y : Submodule D V}
    (hd : Disjoint Y (h.orthogonal X)) (hdim : finrank D Y = finrank D X) {ι : Type*}
    [DecidableEq ι] (b : Module.Basis ι D X) :
    ∃ c : ι → V, (∀ j, c j ∈ Y) ∧ ∀ i j, h (b i) (c j) = if i = j then 1 else 0 := by
  choose c hcY hc using fun j => exists_mem_forall_apply_eq hd hdim (b.coord j)
  refine ⟨c, hcY, fun i j => ?_⟩
  rw [hc j (b i), Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]

/-- `2⁻¹` commutes with everything. -/
theorem two_inv_commute' (h2 : (2 : D) ≠ 0) (a : D) : (2 : D)⁻¹ * a = a * (2 : D)⁻¹ := by
  have : (2 : D) * a = a * 2 := by rw [two_mul, mul_two]
  calc (2 : D)⁻¹ * a = (2 : D)⁻¹ * (a * 2) * (2 : D)⁻¹ := by
        rw [mul_assoc, mul_assoc, mul_inv_cancel₀ h2, mul_one]
    _ = (2 : D)⁻¹ * (2 * a) * (2 : D)⁻¹ := by rw [this]
    _ = a * (2 : D)⁻¹ := by rw [← mul_assoc, inv_mul_cancel₀ h2, one_mul]

/-! ### The dual partner of a totally isotropic subspace (GKT Lemma 4.11 (a)) -/

section Partner

variable [FiniteDimensional D V] [NeZero (2 : D)]

omit [FiniteDimensional D V] in
private theorem two_inv_commute (a : D) : (2 : D)⁻¹ * a = a * (2 : D)⁻¹ := by
  have h2 : (2 : D) ≠ 0 := NeZero.ne 2
  have : (2 : D) * a = a * 2 := by rw [two_mul, mul_two]
  calc (2 : D)⁻¹ * a = (2 : D)⁻¹ * (a * 2) * (2 : D)⁻¹ := by
        rw [mul_assoc, mul_assoc, mul_inv_cancel₀ h2, mul_one]
    _ = (2 : D)⁻¹ * (2 * a) * (2 : D)⁻¹ := by rw [this]
    _ = a * (2 : D)⁻¹ := by rw [← mul_assoc, inv_mul_cancel₀ h2, one_mul]

omit [FiniteDimensional D V] [NeZero (2 : D)] in
private theorem conj_two_inv : conj τ (2 : D)⁻¹ = (2 : D)⁻¹ := by
  rw [RingInvo.conj_inv, RingInvo.conj_two]

/-- GKT Lemma 4.11 (a): a totally isotropic subspace `X` of a non-degenerate space has a totally
isotropic partner `X*` of the same dimension with `V = X^⊥ ⊕ X*`. -/
theorem exists_isTotallyIsotropic_isCompl (hh : h.Nondegenerate) {X : Submodule D V}
    (hX : h.IsTotallyIsotropic X) :
    ∃ X' : Submodule D V, h.IsTotallyIsotropic X' ∧ finrank D X' = finrank D X ∧
      IsCompl (h.orthogonal X) X' := by
  classical
  obtain ⟨Z, hZ⟩ := Submodule.exists_isCompl (h.orthogonal X)
  have hdimZ : finrank D Z = finrank D X := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hZ
    have h2 := finrank_add_finrank_orthogonal hh X
    omega
  set b := Module.finBasis D X
  set m := finrank D X
  obtain ⟨z, hzZ, hz⟩ := exists_dual_family hZ.disjoint.symm hdimZ b
  set a : Fin m → Fin m → D := fun i j => -((2 : D)⁻¹ * h (z i) (z j))
  set z' : Fin m → V := fun j => z j + ∑ k, a j k • ((b k : X) : V)
  have hbz' : ∀ i j, h ((b i : X) : V) (z' j) = if i = j then 1 else 0 := by
    intro i j
    show h _ (z j + ∑ k, a j k • ((b k : X) : V)) = _
    rw [h.map_add_right, h.map_sum_right, hz i j,
      Finset.sum_eq_zero fun k _ => by rw [h.map_smul_right, hX _ (b i).2 _ (b k).2, zero_mul],
      add_zero]
  have hzb : ∀ i k, h (z i) ((b k : X) : V) = if k = i then ((ε : ℤ) : D) else 0 := by
    intro i k
    rw [h.conj_swap, hz k i]
    split_ifs <;> simp
  have hz'z' : ∀ i j, h (z' i) (z' j) = 0 := by
    intro i j
    have e1 : h (z' i) (z' j) = h (z i) (z' j) + a i j := by
      show h (z i + ∑ k, a i k • ((b k : X) : V)) (z' j) = _
      rw [h.map_add_left, h.map_sum_left]
      congr 1
      simp only [h.map_smul_left, hbz', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
    have e2 : h (z i) (z' j) = h (z i) (z j) + ((ε : ℤ) : D) * conj τ (a j i) := by
      show h (z i) (z j + ∑ k, a j k • ((b k : X) : V)) = _
      rw [h.map_add_right, h.map_sum_right]
      congr 1
      simp only [h.map_smul_right, hzb, ite_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
    rw [e1, e2]
    simp only [a, RingInvo.conj_neg, RingInvo.conj_mul, conj_two_inv]
    have hc : conj τ (h (z j) (z i)) = ((ε : ℤ) : D) * h (z i) (z j) := h.conj_apply _ _
    rw [hc, mul_neg, ← mul_assoc ((ε : ℤ) : D), ← mul_assoc ((ε : ℤ) : D),
      units_int_cast_mul_self', one_mul, ← two_inv_commute]
    have h2 : (2 : D) ≠ 0 := NeZero.ne 2
    have : h (z i) (z j) = (2 : D)⁻¹ * h (z i) (z j) + (2 : D)⁻¹ * h (z i) (z j) := by
      rw [← add_mul, ← two_mul, mul_inv_cancel₀ h2, one_mul]
    rw [← sub_eq_add_neg, ← sub_eq_add_neg, sub_sub, ← this, sub_self]
  set X' := Submodule.span D (Set.range z')
  have hX'iso : h.IsTotallyIsotropic X' := by
    intro u hu v hv
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D).1 hu
    obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D).1 hv
    rw [h.map_sum_left]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [h.map_smul_left, h.map_sum_right]
    rw [Finset.sum_eq_zero fun j _ => by rw [h.map_smul_right, hz'z', zero_mul], mul_zero]
  have hcoef : ∀ c : Fin m → D, ∀ i, h ((b i : X) : V) (∑ j, c j • z' j) = conj τ (c i) := by
    intro c i
    rw [h.map_sum_right]
    simp only [h.map_smul_right, hbz', ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
  have hli : LinearIndependent D z' := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have := hcoef c i
    rw [hc, map_zero_right] at this
    exact (RingInvo.conj_eq_zero_iff τ).1 this.symm
  have hdisj : Disjoint (h.orthogonal X) X' := by
    rw [Submodule.disjoint_def]
    intro v hv hv'
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D).1 hv'
    have hc : ∀ i, c i = 0 := fun i => by
      have := hcoef c i
      rw [mem_orthogonal'.1 hv _ (b i).2] at this
      exact (RingInvo.conj_eq_zero_iff τ).1 this.symm
    simp [hc]
  have hdimX' : finrank D X' = m := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  refine ⟨X', hX'iso, hdimX', hdisj, codisjoint_iff.2 ?_⟩
  apply Submodule.eq_top_of_finrank_eq
  have := Submodule.finrank_sup_add_finrank_inf_eq (h.orthogonal X) X'
  rw [disjoint_iff.1 hdisj, finrank_bot, add_zero, hdimX'] at this
  have h2 := finrank_add_finrank_orthogonal hh X
  omega

end Partner

/-- If `V = X^⊥ ⊕ X'` with `X`, `X'` totally isotropic in a non-degenerate space, the form is
non-degenerate on `X ⊕ X'` (GKT Lemma 4.11 (a), Lemma 4.19). -/
theorem restrict_sup_nondegenerate (hh : h.Nondegenerate) {X X' : Submodule D V}
    (hX : h.IsTotallyIsotropic X) (hc : IsCompl (h.orthogonal X) X') :
    (h.restrict (X ⊔ X')).Nondegenerate := by
  rw [restrict_nondegenerate_iff, eq_bot_iff]
  rintro v ⟨hv, hv'⟩
  obtain ⟨x, hx, x', hx', rfl⟩ := Submodule.mem_sup.1 hv
  have hx'X : x' ∈ h.orthogonal X := by
    intro u hu
    have := hv' u (Submodule.mem_sup_left hu)
    rwa [h.map_add_left, (h.apply_eq_zero_comm).1 (hX u hu x hx), zero_add] at this
  have hx'0 : x' = 0 := Submodule.disjoint_def.1 hc.disjoint x' hx'X hx'
  subst hx'0
  rw [add_zero] at hv' ⊢
  have hall : ∀ u, h x u = 0 := by
    intro u
    have : u ∈ h.orthogonal X ⊔ X' := by rw [hc.sup_eq_top]; trivial
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 this
    rw [h.map_add_right, (h.apply_eq_zero_comm).1 (hp x hx)]
    simpa using hv' q (Submodule.mem_sup_right hq)
  exact (Submodule.mem_bot D).2 (hh x hall)

/-- `X ∩ X' = 0` for a dual partner `X'` of a totally isotropic `X`. -/
theorem disjoint_of_isCompl_orthogonal {X X' : Submodule D V} (hX : h.IsTotallyIsotropic X)
    (hc : IsCompl (h.orthogonal X) X') : Disjoint X X' :=
  hc.disjoint.mono_left (isTotallyIsotropic_iff_le_orthogonal.1 hX)

/-! ### Hyperbolic pairs (GKT Proposition B.9, Definition B.10) -/

variable (h) in
/-- A hyperbolic pair: `h x x = h y y = 0` and `h x y = 1`, a standard basis of a hyperbolic plane
(GKT Definition B.10). -/
def IsHyperbolicPair (x y : V) : Prop := h x x = 0 ∧ h y y = 0 ∧ h x y = 1

theorem IsHyperbolicPair.apply_symm {x y : V} (hp : h.IsHyperbolicPair x y) :
    h y x = ((ε : ℤ) : D) := by
  rw [h.conj_swap, hp.2.2, RingInvo.conj_one, mul_one]

/-- A non-zero vector of a non-degenerate space has a partner `z` with `h x z = 1`. -/
theorem exists_apply_eq_one (hh : h.Nondegenerate) {x : V} (hx0 : x ≠ 0) : ∃ z, h x z = 1 := by
  obtain ⟨z, hz⟩ : ∃ z, h x z ≠ 0 := by
    by_contra H
    exact hx0 (hh x fun y => not_not.1 fun hy => H ⟨y, hy⟩)
  refine ⟨conj τ (h x z)⁻¹ • z, ?_⟩
  rw [h.map_smul_right, conj_conj, mul_inv_cancel₀ hz]

/-- A non-zero isotropic vector of a non-degenerate space lies in a hyperbolic pair
(GKT Proposition B.9; `2` is invertible). -/
theorem exists_isHyperbolicPair [NeZero (2 : D)] (hh : h.Nondegenerate) {x : V} (hx : h x x = 0)
    (hx0 : x ≠ 0) : ∃ y, h.IsHyperbolicPair x y := by
  obtain ⟨z, hz⟩ := exists_apply_eq_one hh hx0
  set t : D := -((2 : D)⁻¹ * h z z)
  refine ⟨z + t • x, hx, ?_, ?_⟩
  · have hzx : h z x = ((ε : ℤ) : D) := by rw [h.conj_swap, hz, RingInvo.conj_one, mul_one]
    rw [h.map_add_left, h.map_add_right, h.map_add_right, h.map_smul_left, h.map_smul_left,
      h.map_smul_right, h.map_smul_right, hx, hz, hzx]
    simp only [mul_zero, zero_mul, add_zero, mul_one, t, RingInvo.conj_neg, RingInvo.conj_mul,
      RingInvo.conj_inv, RingInvo.conj_two, h.conj_apply_self]
    have h2 : (2 : D) ≠ 0 := NeZero.ne 2
    have hcomm : ∀ a : D, (2 : D)⁻¹ * a = a * (2 : D)⁻¹ := two_inv_commute' h2
    rw [mul_neg, ← mul_assoc, ← mul_assoc, units_int_cast_mul_self', one_mul, ← hcomm]
    have : h z z = (2 : D)⁻¹ * h z z + (2 : D)⁻¹ * h z z := by
      rw [← add_mul, ← two_mul, mul_inv_cancel₀ h2, one_mul]
    rw [← sub_eq_add_neg, ← sub_eq_add_neg, sub_sub, ← this, sub_self]
  · rw [h.map_add_right, h.map_smul_right, hz, hx, zero_mul, add_zero]

/-! ### The form on a quotient by part of the radical; the space `M^⊥/M` (GKT Lemma 4.14) -/

variable (h) in
/-- The form induced on `V ⧸ N` by a submodule `N` of the radical. -/
def quotient (N : Submodule D V) (hN : ∀ n ∈ N, ∀ v, h n v = 0) :
    EpsilonHermitianForm τ ε (V ⧸ N) where
  toFun a b := Quotient.liftOn₂ a b (fun x y => h x y) (by
    intro x₁ y₁ x₂ y₂ hx hy
    have hx' : x₁ - x₂ ∈ N := (Submodule.quotientRel_def N).1 hx
    have hy' : y₁ - y₂ ∈ N := (Submodule.quotientRel_def N).1 hy
    have e1 : h x₁ y₁ - h x₂ y₁ = 0 := by rw [← h.map_sub_left, hN _ hx']
    have e2 : h x₂ y₁ - h x₂ y₂ = 0 := by
      rw [← h.map_sub_right, h.apply_eq_zero_comm, hN _ hy']
    exact (sub_eq_zero.1 e1).trans (sub_eq_zero.1 e2))
  map_add_left' a b c := by
    induction a using Submodule.Quotient.induction_on
    induction b using Submodule.Quotient.induction_on
    induction c using Submodule.Quotient.induction_on
    rw [← Submodule.Quotient.mk_add]
    exact h.map_add_left _ _ _
  map_smul_left' a x y := by
    induction x using Submodule.Quotient.induction_on
    induction y using Submodule.Quotient.induction_on
    rw [← Submodule.Quotient.mk_smul]
    exact h.map_smul_left _ _ _
  conj_swap' x y := by
    induction x using Submodule.Quotient.induction_on
    induction y using Submodule.Quotient.induction_on
    exact h.conj_swap _ _

@[simp] theorem quotient_apply_mk (N : Submodule D V) (hN : ∀ n ∈ N, ∀ v, h n v = 0) (x y : V) :
    h.quotient N hN (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = h x y := rfl

variable (h) in
/-- The space `W_M = M^⊥/M` of GKT Lemma 4.14. -/
abbrev ReductionSpace (M : Submodule D V) : Type _ :=
  h.orthogonal M ⧸ M.comap (h.orthogonal M).subtype

variable (h) in
/-- The form `⟨w + M, w' + M⟩_M = ⟨w, w'⟩` on `M^⊥/M` for a totally isotropic `M`
(GKT Lemma 4.14). -/
def reduction (M : Submodule D V) : EpsilonHermitianForm τ ε (h.ReductionSpace M) :=
  (h.restrict (h.orthogonal M)).quotient (M.comap (h.orthogonal M).subtype) (by
    intro n hn v
    exact (h.apply_eq_zero_comm).1 (v.2 n hn))

variable (h) in
/-- The quotient map `M^⊥ → M^⊥/M`. -/
abbrev reductionMap (M : Submodule D V) : h.orthogonal M →ₗ[D] h.ReductionSpace M :=
  (M.comap (h.orthogonal M).subtype).mkQ

@[simp] theorem reduction_apply_mk (M : Submodule D V) (x y : h.orthogonal M) :
    h.reduction M (h.reductionMap M x) (h.reductionMap M y) = h x y := rfl

theorem reductionMap_eq_zero_iff {M : Submodule D V} {x : h.orthogonal M} :
    h.reductionMap M x = 0 ↔ (x : V) ∈ M := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
    Submodule.coe_subtype]

theorem reductionMap_surjective (M : Submodule D V) : Function.Surjective (h.reductionMap M) :=
  Submodule.mkQ_surjective _

/-- The form on `M^⊥/M` is non-degenerate (GKT Lemma 4.14). -/
theorem reduction_nondegenerate [FiniteDimensional D V] (hh : h.Nondegenerate)
    (M : Submodule D V) : (h.reduction M).Nondegenerate := by
  intro a ha
  obtain ⟨x, rfl⟩ := h.reductionMap_surjective M a
  rw [reductionMap_eq_zero_iff]
  have : (x : V) ∈ h.orthogonal (h.orthogonal M) := fun y hy => ha (h.reductionMap M ⟨y, hy⟩)
  rwa [orthogonal_orthogonal hh] at this

end EpsilonHermitianForm

end Langlands

end
