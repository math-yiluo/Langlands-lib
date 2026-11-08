import Langlands.LinearAlgebra.RootDatumOrbitPairs

/-! # Simple roots reversed along a path -/

noncomputable section

open Set Function

set_option autoImplicit false

namespace Langlands.LinearAlgebra.RootDatumReversedPath

open Langlands.LinearAlgebra.RootDatumOrbitPairs

section Core

open scoped Classical

variable {ι M N : Type*} [Fintype ι] [AddCommGroup M] [AddCommGroup N]
    {P : RootDatum ι M N} {b : P.Base}

private theorem rootForm_root_root (i j : ι) :
    P.RootForm (P.root i) (P.root j) = ∑ k, P.pairing i k * P.pairing j k := by
  simp [RootPairing.rootForm_apply_apply]

private theorem rootForm_root_equiv (e : ι ≃ ι)
    (he : ∀ i j, P.pairing (e i) (e j) = P.pairing i j) (i j : ι) :
    P.RootForm (P.root (e i)) (P.root (e j)) = P.RootForm (P.root i) (P.root j) := by
  rw [rootForm_root_root, rootForm_root_root, ← Equiv.sum_comp e]
  simp only [he]

private theorem rootForm_comm (x y : M) : P.RootForm x y = P.RootForm y x := by
  simp only [RootPairing.rootForm_apply_apply, mul_comm]

private theorem two_mul_rootForm_root_root (i j : ι) :
    2 * P.RootForm (P.root i) (P.root j) =
      P.pairing j i * P.RootForm (P.root i) (P.root i) := by
  have h := congrArg (P.toLinearMap (P.root j)) (P.rootForm_self_smul_coroot i)
  simp only [map_smul, map_nsmul, RootPairing.root_coroot_eq_pairing,
    RootPairing.toLinearMap_apply_apply_Polarization, smul_eq_mul, nsmul_eq_mul] at h
  push_cast at h
  linarith

private theorem rootForm_pos {x : M} (hx : x ∈ P.rootSpan ℤ) (hx0 : x ≠ 0) :
    0 < P.RootForm x x := by
  rw [RootPairing.rootForm_apply_apply]
  have hnonneg : ∀ k ∈ Finset.univ, 0 ≤ P.coroot' k x * P.coroot' k x :=
    fun k _ => mul_self_nonneg _
  rcases (Finset.sum_nonneg hnonneg).lt_or_eq with h | h
  · exact h
  · exfalso
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp h.symm
    have hker : x ∈ LinearMap.ker P.RootForm := by
      rw [LinearMap.mem_ker]
      ext y
      rw [RootPairing.rootForm_apply_apply, LinearMap.zero_apply]
      refine Finset.sum_eq_zero fun k hk => ?_
      have := hzero k hk
      rw [mul_self_eq_zero] at this
      rw [this, zero_mul]
    exact hx0 ((Submodule.disjoint_def.mp P.disjoint_rootSpan_ker_rootForm) x hx hker)

omit [Fintype ι] in
private theorem pairing_eq_pairingIn (i j : ι) : P.pairing i j = P.pairingIn ℤ i j := by
  rw [← P.algebraMap_pairingIn ℤ i j]
  rfl

private theorem pairing_le_zero {u v : b.support} (h : u ≠ v) :
    P.pairing (u : ι) (v : ι) ≤ 0 := by
  rw [pairing_eq_pairingIn]
  exact b.pairingIn_le_zero_of_ne (fun h' => h (Subtype.ext h')) u.2 v.2

omit [Fintype ι] in
private theorem pairing_ne_zero_symm {u v : ι} (h : P.pairing u v ≠ 0) :
    P.pairing v u ≠ 0 :=
  fun e => h (P.pairing_eq_zero_iff'.mp e)

private theorem norm_pos (u : b.support) : 0 < P.RootForm (P.root (u : ι)) (P.root (u : ι)) :=
  rootForm_pos (Submodule.subset_span (Set.mem_range_self _)) (P.ne_zero u)

private theorem rootForm_le_zero {u v : b.support} (h : u ≠ v) :
    P.RootForm (P.root (u : ι)) (P.root (v : ι)) ≤ 0 := by
  have h2 := two_mul_rootForm_root_root (P := P) (u : ι) (v : ι)
  have := pairing_le_zero h.symm
  have := norm_pos u
  nlinarith

private theorem rootForm_eq_zero {u v : b.support} (h : P.pairing (v : ι) (u : ι) = 0) :
    P.RootForm (P.root (u : ι)) (P.root (v : ι)) = 0 := by
  have h2 := two_mul_rootForm_root_root (P := P) (u : ι) (v : ι)
  rw [h, zero_mul] at h2
  linarith

private theorem two_mul_rootForm_le {u v : b.support} (h : u ≠ v)
    (h0 : P.pairing (v : ι) (u : ι) ≠ 0) :
    2 * P.RootForm (P.root (u : ι)) (P.root (v : ι)) ≤
      - P.RootForm (P.root (u : ι)) (P.root (u : ι)) := by
  have h2 := two_mul_rootForm_root_root (P := P) (u : ι) (v : ι)
  have h1 : P.pairing (v : ι) (u : ι) ≤ -1 := by
    have := pairing_le_zero h.symm
    omega
  have := norm_pos u
  nlinarith

/-! ### Test vectors -/

private theorem rootForm_add_add (X Y : M) :
    P.RootForm (X + Y) (X + Y) = P.RootForm X X + 2 * P.RootForm X Y + P.RootForm Y Y := by
  simp only [map_add, LinearMap.add_apply]
  linear_combination rootForm_comm (P := P) Y X

private theorem rootForm_smul_add_add (S X Y : M) (c : ℤ) :
    P.RootForm (c • S + (X + Y)) (c • S + (X + Y)) =
      c * c * P.RootForm S S + 2 * c * P.RootForm S X + 2 * c * P.RootForm S Y +
        P.RootForm X X + 2 * P.RootForm X Y + P.RootForm Y Y := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  linear_combination c * rootForm_comm (P := P) X S + c * rootForm_comm (P := P) Y S +
    rootForm_comm (P := P) Y X

private theorem rootForm_two_smul_add_four (S X Y Z T : M) :
    P.RootForm ((2 : ℤ) • S + (X + (Y + (Z + T)))) ((2 : ℤ) • S + (X + (Y + (Z + T)))) =
      4 * P.RootForm S S + 4 * (P.RootForm S X + P.RootForm S Y + P.RootForm S Z +
        P.RootForm S T) + (P.RootForm X X + P.RootForm Y Y + P.RootForm Z Z + P.RootForm T T) +
        2 * (P.RootForm X Y + P.RootForm X Z + P.RootForm X T + P.RootForm Y Z +
          P.RootForm Y T + P.RootForm Z T) := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  linear_combination 2 * rootForm_comm (P := P) X S + 2 * rootForm_comm (P := P) Y S +
    2 * rootForm_comm (P := P) Z S + 2 * rootForm_comm (P := P) T S +
    rootForm_comm (P := P) Y X + rootForm_comm (P := P) Z X + rootForm_comm (P := P) T X +
    rootForm_comm (P := P) Z Y + rootForm_comm (P := P) T Y + rootForm_comm (P := P) T Z

/-- A combination `c • ∑_W α + ∑_E α` of simple roots over disjoint sets, with `E`
nonempty, has positive canonical norm. -/
private theorem testVector_pos (W E : Finset b.support) (hWE : Disjoint W E) (c : ℤ)
    {x : b.support} (hx : x ∈ E) :
    0 < P.RootForm (c • ∑ u ∈ W, P.root (u : ι) + ∑ u ∈ E, P.root (u : ι))
      (c • ∑ u ∈ W, P.root (u : ι) + ∑ u ∈ E, P.root (u : ι)) := by
  have hspan : ∀ F : Finset b.support, ∑ u ∈ F, P.root (u : ι) ∈ P.rootSpan ℤ :=
    fun F => Submodule.sum_mem _ fun u _ => Submodule.subset_span (Set.mem_range_self _)
  refine rootForm_pos (Submodule.add_mem _ (Submodule.smul_mem _ _ (hspan W)) (hspan E)) ?_
  intro h0
  let g : b.support → ℤ := fun u => if u ∈ E then 1 else c
  have hsum : ∑ u ∈ W ∪ E, g u • P.root (u : ι) = 0 := by
    rw [Finset.sum_union hWE, ← h0, Finset.smul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun u hu => ?_
      simp [g, Finset.disjoint_left.mp hWE hu]
    · refine Finset.sum_congr rfl fun u hu => ?_
      simp [g, hu]
  have := linearIndependent_iff'.mp b.linearIndepOn_root.linearIndependent (W ∪ E) g hsum x
    (Finset.mem_union_right _ hx)
  simp [g, hx] at this

private theorem testVector₁ {W : Finset b.support} {x : b.support} (hxW : x ∉ W) :
    0 < P.RootForm (∑ u ∈ W, P.root (u : ι)) (∑ u ∈ W, P.root (u : ι)) +
      2 * P.RootForm (∑ u ∈ W, P.root (u : ι)) (P.root (x : ι)) +
        P.RootForm (P.root (x : ι)) (P.root (x : ι)) := by
  have h := testVector_pos (P := P) W {x} (Finset.disjoint_singleton_right.mpr hxW) 1
    (Finset.mem_singleton_self x)
  rwa [one_smul, Finset.sum_singleton, rootForm_add_add] at h

private theorem testVector₂ {W : Finset b.support} {x y : b.support} (hxW : x ∉ W)
    (hyW : y ∉ W) (hxy : x ≠ y) (c : ℤ) :
    0 < c * c * P.RootForm (∑ u ∈ W, P.root (u : ι)) (∑ u ∈ W, P.root (u : ι)) +
      2 * c * P.RootForm (∑ u ∈ W, P.root (u : ι)) (P.root (x : ι)) +
      2 * c * P.RootForm (∑ u ∈ W, P.root (u : ι)) (P.root (y : ι)) +
      P.RootForm (P.root (x : ι)) (P.root (x : ι)) +
      2 * P.RootForm (P.root (x : ι)) (P.root (y : ι)) +
      P.RootForm (P.root (y : ι)) (P.root (y : ι)) := by
  have hd : Disjoint W {x, y} := by
    rw [Finset.disjoint_insert_right, Finset.disjoint_singleton_right]
    exact ⟨hxW, hyW⟩
  have h := testVector_pos (P := P) W {x, y} hd c (Finset.mem_insert_self x _)
  rwa [Finset.sum_pair hxy, rootForm_smul_add_add] at h

private theorem testVector₄ {W : Finset b.support} {x y z w : b.support} (hxW : x ∉ W)
    (hyW : y ∉ W) (hzW : z ∉ W) (hwW : w ∉ W) (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    0 < 4 * P.RootForm (∑ u ∈ W, P.root (u : ι)) (∑ u ∈ W, P.root (u : ι)) +
      4 * (P.RootForm (∑ u ∈ W, P.root (u : ι)) (P.root (x : ι)) +
        P.RootForm (∑ u ∈ W, P.root (u : ι)) (P.root (y : ι)) +
        P.RootForm (∑ u ∈ W, P.root (u : ι)) (P.root (z : ι)) +
        P.RootForm (∑ u ∈ W, P.root (u : ι)) (P.root (w : ι))) +
      (P.RootForm (P.root (x : ι)) (P.root (x : ι)) +
        P.RootForm (P.root (y : ι)) (P.root (y : ι)) +
        P.RootForm (P.root (z : ι)) (P.root (z : ι)) +
        P.RootForm (P.root (w : ι)) (P.root (w : ι))) +
      2 * (P.RootForm (P.root (x : ι)) (P.root (y : ι)) +
        P.RootForm (P.root (x : ι)) (P.root (z : ι)) +
        P.RootForm (P.root (x : ι)) (P.root (w : ι)) +
        P.RootForm (P.root (y : ι)) (P.root (z : ι)) +
        P.RootForm (P.root (y : ι)) (P.root (w : ι)) +
        P.RootForm (P.root (z : ι)) (P.root (w : ι))) := by
  have hd : Disjoint W {x, y, z, w} := by
    simp only [Finset.disjoint_insert_right, Finset.disjoint_singleton_right]
    exact ⟨hxW, hyW, hzW, hwW⟩
  have h := testVector_pos (P := P) W {x, y, z, w} hd 2 (Finset.mem_insert_self x _)
  rwa [Finset.sum_insert (by simp [hxy, hxz, hxw]), Finset.sum_insert (by simp [hyz, hyw]),
    Finset.sum_pair hzw, rootForm_two_smul_add_four] at h

/-! ### Half paths -/

/-- The permutation preserves the pairing and the canonical form on simple roots. -/
private def Preserves (σ : Equiv.Perm b.support) : Prop :=
  (∀ u v : b.support, P.pairing (σ u : ι) (σ v : ι) = P.pairing (u : ι) (v : ι)) ∧
    ∀ u v : b.support, P.RootForm (P.root (σ u : ι)) (P.root (σ v : ι)) =
      P.RootForm (P.root (u : ι)) (P.root (v : ι))

/-- A half path `p 0 = a, p 1, …, p (k - 1)` together with its image under `σ`,
whose union is `W`, forming a simply-laced path reversed by `σ`, with sum of
roots of norm equal to the norm of `a`, and with every outside simple root
orthogonal to all of `W` except possibly the two ends `p (k - 1)`, `σ (p (k - 1))`. -/
private structure IsHalfPath (σ : Equiv.Perm b.support) (a : b.support) (p : ℕ → b.support)
    (k : ℕ) (W : Finset b.support) : Prop where
  pos : 0 < k
  zero : p 0 = a
  invol : ∀ i < k, σ (σ (p i)) = p i
  norm : ∀ i < k, P.RootForm (P.root (p i : ι)) (P.root (p i : ι)) =
    P.RootForm (P.root (a : ι)) (P.root (a : ι))
  pp : ∀ i < k, ∀ j < k, P.pairing (p i : ι) (p j : ι) =
    if i = j then 2 else if i + 1 = j ∨ j + 1 = i then -1 else 0
  pq : ∀ i < k, ∀ j < k, P.pairing (p i : ι) (σ (p j) : ι) = if i = 0 ∧ j = 0 then -1 else 0
  mem : ∀ u, u ∈ W ↔ ∃ i < k, u = p i ∨ u = σ (p i)
  sum : P.RootForm (∑ u ∈ W, P.root (u : ι)) (∑ u ∈ W, P.root (u : ι)) =
    P.RootForm (P.root (a : ι)) (P.root (a : ι))
  out : ∀ z ∉ W, ∀ i, i + 1 < k →
    P.pairing (z : ι) (p i : ι) = 0 ∧ P.pairing (z : ι) (σ (p i) : ι) = 0
  sumOut : ∀ z ∉ W, P.RootForm (∑ u ∈ W, P.root (u : ι)) (P.root (z : ι)) =
    P.RootForm (P.root (p (k - 1) : ι)) (P.root (z : ι)) +
      P.RootForm (P.root (σ (p (k - 1)) : ι)) (P.root (z : ι))

variable {σ : Equiv.Perm b.support} {a : b.support} {p : ℕ → b.support} {k : ℕ}
  {W : Finset b.support}

private theorem lastMem (h : IsHalfPath σ a p k W) : p (k - 1) ∈ W :=
  (h.mem _).2 ⟨k - 1, by have := h.pos; omega, Or.inl rfl⟩

private theorem σLastMem (h : IsHalfPath σ a p k W) : σ (p (k - 1)) ∈ W :=
  (h.mem _).2 ⟨k - 1, by have := h.pos; omega, Or.inr rfl⟩

private theorem σNotMem (h : IsHalfPath σ a p k W) {z : b.support} (hz : z ∉ W) :
    σ z ∉ W := by
  intro hσz
  obtain ⟨i, hi, hzi | hzi⟩ := (h.mem _).1 hσz
  · apply hz
    refine (h.mem _).2 ⟨i, hi, Or.inr ?_⟩
    apply σ.injective
    rw [hzi, h.invol i hi]
  · exact hz ((h.mem _).2 ⟨i, hi, Or.inl (σ.injective hzi)⟩)

/-- Pairing with an image under an involutive point. -/
private theorem pairing_σ_left (hσ : Preserves σ) {u v : b.support} (hv : σ (σ v) = v) :
    P.pairing (σ u : ι) (v : ι) = P.pairing (u : ι) (σ v : ι) := by
  have := hσ.1 u (σ v)
  rw [hv] at this
  exact this

/-- The facts forced on an outside neighbour `x` of the last vertex. -/
private theorem neighbour (hσ : Preserves σ) (h : IsHalfPath σ a p k W) {x : b.support}
    (hxW : x ∉ W) (hx : P.pairing (x : ι) (p (k - 1) : ι) ≠ 0) :
    P.pairing (x : ι) (σ (p (k - 1)) : ι) = 0 ∧ σ x ∉ W ∧
      P.pairing (σ x : ι) (σ (p (k - 1)) : ι) ≠ 0 ∧ x ≠ σ x ∧
      P.pairing (x : ι) (p (k - 1) : ι) = -1 ∧ P.pairing (p (k - 1) : ι) (x : ι) = -1 ∧
      P.pairing (x : ι) (σ x : ι) = 0 ∧
      P.RootForm (P.root (x : ι)) (P.root (x : ι)) =
        P.RootForm (P.root (a : ι)) (P.root (a : ι)) ∧
      P.RootForm (P.root (σ x : ι)) (P.root (σ x : ι)) =
        P.RootForm (P.root (a : ι)) (P.root (a : ι)) ∧
      2 * P.RootForm (∑ u ∈ W, P.root (u : ι)) (P.root (x : ι)) =
        - P.RootForm (P.root (a : ι)) (P.root (a : ι)) ∧
      2 * P.RootForm (∑ u ∈ W, P.root (u : ι)) (P.root (σ x : ι)) =
        - P.RootForm (P.root (a : ι)) (P.root (a : ι)) := by
  have hk := h.pos
  have hpW := lastMem h
  have hqW := σLastMem h
  have hpp : σ (σ (p (k - 1))) = p (k - 1) := h.invol _ (by omega)
  have hxp : x ≠ p (k - 1) := fun e => hxW (e ▸ hpW)
  have hxq : x ≠ σ (p (k - 1)) := fun e => hxW (e ▸ hqW)
  have hyW : σ x ∉ W := σNotMem h hxW
  have hn := norm_pos (P := P) a
  have hnp := h.norm (k - 1) (by omega)
  have hnx := norm_pos (P := P) x
  have eS := h.sum
  have eSx := h.sumOut x hxW
  have eSy := h.sumOut (σ x) hyW
  have hs1 := two_mul_rootForm_root_root (P := P) (p (k - 1) : ι) (x : ι)
  rw [hnp] at hs1
  have hs2 := two_mul_rootForm_root_root (P := P) (x : ι) (p (k - 1) : ι)
  have cpx := rootForm_comm (P := P) (P.root (x : ι)) (P.root (p (k - 1) : ι))
  have hApx0 : P.pairing (p (k - 1) : ι) (x : ι) ≠ 0 := pairing_ne_zero_symm hx
  have hAxp : P.pairing (x : ι) (p (k - 1) : ι) ≤ -1 := by
    have := pairing_le_zero hxp
    omega
  have hApx : P.pairing (p (k - 1) : ι) (x : ι) ≤ -1 := by
    have := pairing_le_zero hxp.symm
    omega
  -- the neighbour is orthogonal to the other end
  have ha : P.pairing (x : ι) (σ (p (k - 1)) : ι) = 0 := by
    by_contra hq
    have t := testVector₁ (P := P) hxW
    have h1 := two_mul_rootForm_le hxp.symm hx
    have h2 := two_mul_rootForm_le hxq (pairing_ne_zero_symm hq)
    have c2 := rootForm_comm (P := P) (P.root (x : ι)) (P.root (σ (p (k - 1)) : ι))
    linarith
  have hyq : P.pairing (σ x : ι) (σ (p (k - 1)) : ι) ≠ 0 := by
    rw [hσ.1]
    exact hx
  have hyp : P.pairing (σ x : ι) (p (k - 1) : ι) = 0 := by
    rw [pairing_σ_left hσ hpp]
    exact ha
  have hxy : x ≠ σ x := by
    intro e
    apply hyq
    rw [← e]
    exact ha
  have hBqx : P.RootForm (P.root (σ (p (k - 1)) : ι)) (P.root (x : ι)) = 0 :=
    rootForm_eq_zero ha
  have hBpy : P.RootForm (P.root (p (k - 1) : ι)) (P.root (σ x : ι)) = 0 :=
    rootForm_eq_zero hyp
  have hBqy := hσ.2 (p (k - 1)) x
  have hny := hσ.2 x x
  have hBxy := rootForm_le_zero hxy
  have t1 := testVector₂ (P := P) hxW hyW hxy 1
  have t2 := testVector₂ (P := P) hxW hyW hxy 2
  -- the bond to the last vertex is simple
  have hd1 : P.pairing (x : ι) (p (k - 1) : ι) = -1 := by
    by_contra hne
    have hle : P.pairing (x : ι) (p (k - 1) : ι) ≤ -2 := by omega
    have e1 : 2 * P.RootForm (P.root (p (k - 1) : ι)) (P.root (x : ι)) ≤
        -2 * P.RootForm (P.root (a : ι)) (P.root (a : ι)) := by nlinarith
    have e2 : 2 * P.RootForm (P.root (x : ι)) (P.root (p (k - 1) : ι)) ≤
        - P.RootForm (P.root (x : ι)) (P.root (x : ι)) := by nlinarith
    linarith
  have hd2 : P.pairing (p (k - 1) : ι) (x : ι) = -1 := by
    by_contra hne
    have hle : P.pairing (p (k - 1) : ι) (x : ι) ≤ -2 := by omega
    have e1 : 2 * P.RootForm (P.root (p (k - 1) : ι)) (P.root (x : ι)) ≤
        - P.RootForm (P.root (a : ι)) (P.root (a : ι)) := by nlinarith
    have e2 : 2 * P.RootForm (P.root (x : ι)) (P.root (p (k - 1) : ι)) ≤
        -2 * P.RootForm (P.root (x : ι)) (P.root (x : ι)) := by nlinarith
    linarith
  rw [hd1] at hs1
  rw [hd2] at hs2
  have hnxa : P.RootForm (P.root (x : ι)) (P.root (x : ι)) =
      P.RootForm (P.root (a : ι)) (P.root (a : ι)) := by linarith
  -- the neighbour and its image are orthogonal
  have he : P.pairing (x : ι) (σ x : ι) = 0 := by
    by_contra hne
    have e1 := two_mul_rootForm_le hxy (pairing_ne_zero_symm hne)
    linarith
  exact ⟨ha, hyW, hyq, hxy, hd1, hd2, he, hnxa, by linarith, by linarith, by linarith⟩

/-- The last vertex has at most one outside neighbour. -/
private theorem neighbour_unique (hσ : Preserves σ) (h : IsHalfPath σ a p k W)
    {x z : b.support} (hxW : x ∉ W) (hx : P.pairing (x : ι) (p (k - 1) : ι) ≠ 0)
    (hzW : z ∉ W) (hz : P.pairing (z : ι) (p (k - 1) : ι) ≠ 0) : z = x := by
  by_contra hzx
  obtain ⟨xa, hyW, hyq, hxy, -, -, -, hnx, hny, hSx, hSy⟩ := neighbour hσ h hxW hx
  obtain ⟨za, hwW, hwq, hzw, -, -, -, hnz, hnw, hSz, hSw⟩ := neighbour hσ h hzW hz
  have hzy : z ≠ σ x := fun e => hyq (e ▸ za)
  have hwx : σ z ≠ x := fun e => hwq (e.symm ▸ xa)
  have hwy : σ z ≠ σ x := fun e => hzx (σ.injective e)
  have t := testVector₄ (P := P) hxW hyW hzW hwW hxy (Ne.symm hzx) (Ne.symm hwx)
    (Ne.symm hzy) (Ne.symm hwy) hzw
  have := rootForm_le_zero (P := P) hxy
  have := rootForm_le_zero (P := P) (Ne.symm hzx)
  have := rootForm_le_zero (P := P) (Ne.symm hwx)
  have := rootForm_le_zero (P := P) (Ne.symm hzy)
  have := rootForm_le_zero (P := P) (Ne.symm hwy)
  have := rootForm_le_zero (P := P) hzw
  have := h.sum
  linarith

/-- An outside root other than the new neighbour and its image is orthogonal to
both ends. -/
private theorem outside_ortho (hσ : Preserves σ) (h : IsHalfPath σ a p k W) {x : b.support}
    (hxW : x ∉ W) (hx : P.pairing (x : ι) (p (k - 1) : ι) ≠ 0) {z : b.support} (hzW : z ∉ W)
    (hzx : z ≠ x) (hzy : z ≠ σ x) :
    P.pairing (z : ι) (p (k - 1) : ι) = 0 ∧ P.pairing (z : ι) (σ (p (k - 1)) : ι) = 0 := by
  have hpp : σ (σ (p (k - 1))) = p (k - 1) := h.invol _ (by have := h.pos; omega)
  refine ⟨by_contra fun hz => hzx (neighbour_unique hσ h hxW hx hzW hz), ?_⟩
  by_contra hz
  have hσz : P.pairing (σ z : ι) (p (k - 1) : ι) ≠ 0 := by
    rw [pairing_σ_left hσ hpp]
    exact hz
  have e1 := neighbour_unique hσ h hxW hx (σNotMem h hzW) hσz
  -- `σ (σ x) = x` since `σ (σ x)` is again an outside neighbour
  have hyW := σNotMem h hxW
  have hσσx : P.pairing (σ (σ x) : ι) (p (k - 1) : ι) ≠ 0 := by
    rw [pairing_σ_left hσ hpp, hσ.1]
    exact hx
  have e2 := neighbour_unique hσ h hxW hx (σNotMem h hyW) hσσx
  exact hzy (σ.injective (e1.trans e2.symm))

/-- Extending a half path by an outside neighbour of its last vertex. -/
private theorem extend (hσ : Preserves σ) (h : IsHalfPath σ a p k W) {x : b.support}
    (hxW : x ∉ W) (hx : P.pairing (x : ι) (p (k - 1) : ι) ≠ 0) :
    IsHalfPath σ a (Function.update p k x) (k + 1) (insert x (insert (σ x) W)) := by
  have hk := h.pos
  have hpp : σ (σ (p (k - 1))) = p (k - 1) := h.invol _ (by omega)
  obtain ⟨xa, hyW, hyq, hxy, hd1, hd2, he, hnx, hny, hSx, hSy⟩ := neighbour hσ h hxW hx
  have hσσx : σ (σ x) = x := by
    refine neighbour_unique hσ h hxW hx (σNotMem h hyW) ?_
    rw [pairing_σ_left hσ hpp, hσ.1]
    exact hx
  have hp' : ∀ i < k, Function.update p k x i = p i := fun i hi => by
    rw [Function.update_apply, ite_eq_right (by omega)]
  have hpk : Function.update p k x k = x := by
    rw [Function.update_apply, ite_eq_left rfl]
  have hlt : ∀ i, i < k + 1 → i < k ∨ i = k := fun i hi => by omega
  -- outside data of the new vertex relative to the old path
  have hxo : ∀ j < k, P.pairing (x : ι) (σ (p j) : ι) = 0 := by
    intro j hj
    obtain hj' | hj' : j + 1 < k ∨ j = k - 1 := by omega
    · exact (h.out x hxW j hj').2
    · rw [hj']
      exact xa
  have hxW' : x ∉ insert (σ x) W := by
    rw [Finset.mem_insert, not_or]
    exact ⟨hxy, hxW⟩
  refine
    { pos := by omega
      zero := by rw [hp' 0 hk]; exact h.zero
      invol := ?_
      norm := ?_
      pp := ?_
      pq := ?_
      mem := ?_
      sum := ?_
      out := ?_
      sumOut := ?_ }
  · intro i hi
    rcases hlt i hi with hi | rfl
    · rw [hp' i hi]
      exact h.invol i hi
    · rw [hpk]
      exact hσσx
  · intro i hi
    rcases hlt i hi with hi | rfl
    · rw [hp' i hi]
      exact h.norm i hi
    · rw [hpk]
      exact hnx
  · intro i hi j hj
    rcases hlt i hi with hi | hik <;> rcases hlt j hj with hj | hjk
    · rw [hp' i hi, hp' j hj]
      exact h.pp i hi j hj
    · rw [hjk, hp' i hi, hpk]
      obtain hi' | hi' : i + 1 < k ∨ i = k - 1 := by omega
      · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        exact P.pairing_eq_zero_iff'.mp (h.out x hxW i hi').1
      · rw [ite_eq_right (by omega), ite_eq_left (by omega), hi']
        exact hd2
    · rw [hik, hp' j hj, hpk]
      obtain hj' | hj' : j + 1 < k ∨ j = k - 1 := by omega
      · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        exact (h.out x hxW j hj').1
      · rw [ite_eq_right (by omega), ite_eq_left (by omega), hj']
        exact hd1
    · rw [hik, hjk, hpk, ite_eq_left rfl]
      exact P.pairing_same _
  · intro i hi j hj
    rcases hlt i hi with hi | hik <;> rcases hlt j hj with hj | hjk
    · rw [hp' i hi, hp' j hj]
      exact h.pq i hi j hj
    · rw [hjk, hp' i hi, hpk, ite_eq_right (by omega), ← h.invol i hi, hσ.1]
      exact P.pairing_eq_zero_iff'.mp (hxo i hi)
    · rw [hik, hp' j hj, hpk, ite_eq_right (by omega)]
      exact hxo j hj
    · rw [hik, hjk, hpk, ite_eq_right (by omega)]
      exact he
  · intro u
    constructor
    · intro hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact ⟨k, by omega, Or.inl hpk.symm⟩
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact ⟨k, by omega, Or.inr (by rw [hpk])⟩
      obtain ⟨i, hi, hui⟩ := (h.mem u).1 hu
      exact ⟨i, by omega, by rwa [hp' i hi]⟩
    · rintro ⟨i, hi, hui⟩
      rcases hlt i hi with hi | rfl
      · rw [hp' i hi] at hui
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ((h.mem u).2 ⟨i, hi, hui⟩))
      · rw [hpk] at hui
        rcases hui with rfl | rfl
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  · rw [Finset.sum_insert hxW', Finset.sum_insert hyW, rootForm_add_add, rootForm_add_add]
    have hBxy : P.RootForm (P.root (x : ι)) (P.root (σ x : ι)) = 0 :=
      rootForm_eq_zero (P.pairing_eq_zero_iff'.mp he)
    simp only [map_add]
    have c1 := rootForm_comm (P := P) (P.root (x : ι)) (∑ u ∈ W, P.root (u : ι))
    have c2 := rootForm_comm (P := P) (P.root (σ x : ι)) (∑ u ∈ W, P.root (u : ι))
    have := h.sum
    linarith
  · intro z hz i hi
    rw [Finset.mem_insert, Finset.mem_insert, not_or, not_or] at hz
    obtain ⟨hzx, hzy, hzW⟩ := hz
    rw [hp' i (by omega)]
    obtain hi' | hi' : i + 1 < k ∨ i = k - 1 := by omega
    · exact h.out z hzW i hi'
    · rw [hi']
      exact outside_ortho hσ h hxW hx hzW hzx hzy
  · intro z hz
    rw [Finset.mem_insert, Finset.mem_insert, not_or, not_or] at hz
    obtain ⟨hzx, hzy, hzW⟩ := hz
    obtain ⟨o1, o2⟩ := outside_ortho hσ h hxW hx hzW hzx hzy
    rw [Nat.add_sub_cancel, hpk, Finset.sum_insert hxW', Finset.sum_insert hyW]
    simp only [map_add, LinearMap.add_apply]
    rw [h.sumOut z hzW, rootForm_eq_zero o1, rootForm_eq_zero o2]
    ring

/-- At a terminal half path every outside simple root is orthogonal to all of `W`. -/
private theorem terminal (hσ : Preserves σ) (h : IsHalfPath σ a p k W)
    (hterm : ∀ x ∉ W, P.pairing (x : ι) (p (k - 1) : ι) = 0) {z : b.support} (hz : z ∉ W)
    {u : b.support} (hu : u ∈ W) : P.pairing (z : ι) (u : ι) = 0 := by
  have hk := h.pos
  obtain ⟨i, hi, rfl | rfl⟩ := (h.mem u).1 hu <;>
    obtain hi' | hi' : i + 1 < k ∨ i = k - 1 := by omega
  · exact (h.out z hz i hi').1
  · rw [hi']
    exact hterm z hz
  · exact (h.out z hz i hi').2
  · rw [hi']
    by_contra hne
    apply hne
    have hpp : σ (σ (p (k - 1))) = p (k - 1) := h.invol _ (by omega)
    have := hterm (σ z) (σNotMem h hz)
    rwa [pairing_σ_left hσ hpp] at this

private theorem injOn (h : IsHalfPath σ a p k W) {i j : ℕ} (hi : i < k) (hj : j < k)
    (hij : p i = p j) : i = j := by
  have := h.pp i hi j hj
  rw [hij, P.pairing_same] at this
  split_ifs at this with h1 h2 <;> omega

/-- The initial half path `a`, `σ a`. -/
private theorem initial (hσ : Preserves σ) (h1 : P.pairing (a : ι) (σ a : ι) = -1)
    (h2 : σ (σ a) = a) : IsHalfPath σ a (fun _ => a) 1 {a, σ a} := by
  have hne : a ≠ σ a := by
    intro e
    have := P.pairing_same (a : ι)
    rw [← e] at h1
    omega
  have h1' : P.pairing (σ a : ι) (a : ι) = -1 := by
    rw [pairing_σ_left hσ h2]
    exact h1
  refine
    { pos := by omega
      zero := rfl
      invol := fun _ _ => h2
      norm := fun _ _ => rfl
      pp := ?_
      pq := ?_
      mem := ?_
      sum := ?_
      out := fun _ _ i hi => by omega
      sumOut := ?_ }
  · intro i hi j hj
    obtain rfl : i = 0 := by omega
    obtain rfl : j = 0 := by omega
    simp
  · intro i hi j hj
    obtain rfl : i = 0 := by omega
    obtain rfl : j = 0 := by omega
    simpa using h1
  · intro u
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hu
      exact ⟨0, by omega, hu⟩
    · rintro ⟨i, -, hu⟩
      exact hu
  · rw [Finset.sum_pair hne, rootForm_add_add, hσ.2]
    have := two_mul_rootForm_root_root (P := P) (a : ι) (σ a : ι)
    rw [h1'] at this
    linarith
  · intro z _
    rw [Finset.sum_pair hne]
    simp only [map_add, LinearMap.add_apply]

/-- A terminal half path exists. -/
private theorem exists_terminal (hσ : Preserves σ) (h1 : P.pairing (a : ι) (σ a : ι) = -1)
    (h2 : σ (σ a) = a) :
    ∃ (p : ℕ → b.support) (k : ℕ) (W : Finset b.support), IsHalfPath σ a p k W ∧
      ∀ x ∉ W, P.pairing (x : ι) (p (k - 1) : ι) = 0 := by
  suffices H : ∀ (n : ℕ) (p : ℕ → b.support) (k : ℕ) (W : Finset b.support),
      IsHalfPath σ a p k W → Fintype.card b.support < k + n →
      ∃ (p : ℕ → b.support) (k : ℕ) (W : Finset b.support), IsHalfPath σ a p k W ∧
        ∀ x ∉ W, P.pairing (x : ι) (p (k - 1) : ι) = 0 from
    H (Fintype.card b.support) _ _ _ (initial hσ h1 h2) (by omega)
  intro n
  induction n with
  | zero =>
    intro p k W h hcard
    exfalso
    have hinj : Set.InjOn p (Finset.range k : Set ℕ) := fun i hi j hj hij =>
      injOn h (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij
    have := Finset.card_le_univ ((Finset.range k).image p)
    rw [Finset.card_image_of_injOn hinj, Finset.card_range] at this
    omega
  | succ n ih =>
    intro p k W h hcard
    by_cases hx : ∃ x ∉ W, P.pairing (x : ι) (p (k - 1) : ι) ≠ 0
    · obtain ⟨x, hxW, hx⟩ := hx
      exact ih _ _ _ (extend hσ h hxW hx) (by omega)
    · push Not at hx
      exact ⟨p, k, W, h, hx⟩

end Core

variable {ι M N : Type*} [Finite ι] [AddCommGroup M] [AddCommGroup N]
    {P : RootDatum ι M N} {b : P.Base} {Γ : Type*} [Group Γ]
    {ρ : Γ →* Equiv.Perm b.support}

omit [Finite ι] in
/-- `β` enumerates, in order, a connected component of the Dynkin diagram of the
base `b` of type `A_{2m}`, and the permutation `σ` of the simple roots reverses
it. Simple roots off the path are orthogonal to all of it. -/
structure IsReversedPath (σ : Equiv.Perm b.support) {m : ℕ} (β : Fin (2 * m) → b.support) :
    Prop where
  pos : 0 < m
  injective : Function.Injective β
  pairing_eq : ∀ i j, P.pairing (β i : ι) (β j : ι) =
    if (i : ℕ) = j then 2 else if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then -1 else 0
  apply_eq_rev : ∀ i, σ (β i) = β i.rev
  isOrthogonal : ∀ z, z ∉ Set.range β → ∀ i, P.IsOrthogonal (z : ι) (β i : ι)

/-- If a group element of a pairing-compatible action on the simple roots moves a
simple root `a` to a non-orthogonal one, then the connected component of `a` in
the Dynkin diagram is a path `β 0, …, β (2m - 1)` of type `A_{2m}` reversed by the
element, with `a = β (m - 1)`. -/
theorem exists_isReversedPath (hρ : IsPairingCompatible b ρ) {γ : Γ} {a : b.support}
    (hγ : ρ γ a ≠ a) (hγo : ¬ P.IsOrthogonal (a : ι) (ρ γ a : ι)) :
    ∃ (m : ℕ) (β : Fin (2 * m) → b.support), IsReversedPath (ρ γ) β ∧
      ∀ i : Fin (2 * m), (i : ℕ) + 1 = m → β i = a := by
  classical
  let := Fintype.ofFinite ι
  set σ := ρ γ with hσdef
  have hσ : Preserves σ := by
    obtain ⟨e, he, hρe⟩ := hρ γ
    refine ⟨fun u v => hρ.pairing_apply γ u v, fun u v => ?_⟩
    rw [hρe, hρe, rootForm_root_equiv e he]
  have h1 := (pairing_eq_neg_one_of_not_isOrthogonal hρ a hγ hγo).1
  have h2 := apply_apply_eq_of_not_isOrthogonal hρ a hγ hγo
  obtain ⟨p, k, W, h, hterm⟩ := exists_terminal hσ h1 h2
  have hk := h.pos
  let β : Fin (2 * k) → b.support := fun i =>
    if (i : ℕ) < k then p (k - 1 - i) else σ (p (i - k))
  have hβ1 : ∀ i : Fin (2 * k), (i : ℕ) < k → β i = p (k - 1 - i) := fun i hi => ite_eq_left hi
  have hβ2 : ∀ i : Fin (2 * k), ¬ (i : ℕ) < k → β i = σ (p (i - k)) := fun i hi => ite_eq_right hi
  have hpat : ∀ i j : Fin (2 * k), P.pairing (β i : ι) (β j : ι) =
      if (i : ℕ) = j then 2 else if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then -1 else 0 := by
    intro i j
    have hi2 := i.2
    have hj2 := j.2
    by_cases hi : (i : ℕ) < k <;> by_cases hj : (j : ℕ) < k
    · rw [hβ1 i hi, hβ1 j hj, h.pp _ (by omega) _ (by omega)]
      split_ifs <;> omega
    · rw [hβ1 i hi, hβ2 j hj, h.pq _ (by omega) _ (by omega)]
      split_ifs <;> omega
    · rw [hβ2 i hi, hβ1 j hj, pairing_σ_left hσ (h.invol _ (by omega)),
        h.pq _ (by omega) _ (by omega)]
      split_ifs <;> omega
    · rw [hβ2 i hi, hβ2 j hj, hσ.1, h.pp _ (by omega) _ (by omega)]
      split_ifs <;> omega
  have hmemW : ∀ i, β i ∈ W := by
    intro i
    by_cases hi : (i : ℕ) < k
    · rw [hβ1 i hi]
      exact (h.mem _).2 ⟨_, by omega, Or.inl rfl⟩
    · rw [hβ2 i hi]
      exact (h.mem _).2 ⟨_, by have := i.2; omega, Or.inr rfl⟩
  refine ⟨k, β, ⟨hk, ?_, hpat, ?_, ?_⟩, ?_⟩
  · intro i j hij
    have := hpat i j
    rw [hij, P.pairing_same] at this
    apply Fin.ext
    split_ifs at this with h1 h2 <;> omega
  · intro i
    have hi2 := i.2
    by_cases hi : (i : ℕ) < k
    · rw [hβ1 i hi, hβ2 i.rev (by rw [Fin.val_rev]; omega), Fin.val_rev]
      congr 2
      omega
    · rw [hβ2 i hi, hβ1 i.rev (by rw [Fin.val_rev]; omega), Fin.val_rev,
        h.invol _ (by omega)]
      congr 1
      omega
  · intro z hz i
    have hzW : z ∉ W := by
      intro hzW
      obtain ⟨j, hj, rfl | rfl⟩ := (h.mem z).1 hzW
      · exact hz ⟨⟨k - 1 - j, by omega⟩, by rw [hβ1 _ (by simp; omega)]; congr 1; simp; omega⟩
      · exact hz ⟨⟨k + j, by omega⟩, by rw [hβ2 _ (by simp)]; simp⟩
    have h0 := terminal hσ h hterm hzW (hmemW i)
    exact ⟨h0, P.pairing_eq_zero_iff'.mp h0⟩
  · intro i hi
    rw [hβ1 i (by omega), show k - 1 - (i : ℕ) = 0 by omega]
    exact h.zero

end Langlands.LinearAlgebra.RootDatumReversedPath
