import Langlands.GroupScheme.Composition.SplitCayleyAutomorphism.Interface

/-! # Stable subspaces and rigidity modulo the unit for Zorn's algebra

The two matrix-algebra inputs for the triviality of the unipotent radical of the split Cayley
automorphism group, and the seven-dimensional quotient of Zorn's algebra by the line of the unit.

* `stableSubspace : StableSubspaceStatement`: over an algebraically closed field, a subspace of
  `k⁸` stable under the root groups and containing a vector off the line of the unit contains
  `u₁, u₂, u₃, v₁, v₂, v₃`.
* `unitRigidity : UnitRigidityStatement`: an automorphism matrix moving each of
  `u₁, …, v₃` by a multiple of the unit is the identity.
* `projLin`, `sectLin`, `quotMatrix`: the projection `A⁸ → A⁷` with kernel `A · 1`, a section
  of it, and the induced matrix on the quotient, multiplicative on matrices fixing the unit.
-/

noncomputable section

universe u

open Matrix

namespace Langlands.GroupScheme

namespace SplitCayley

/-! ### Expansion of root-group elements in the parameter -/

section Expansion

variable {A : Type u} [CommRing A]

/-- The coefficient of `r²` in `x_α(r) x`; it vanishes for the long roots. -/
def quadCoeff : Root → (Fin 8 → A) → (Fin 8 → A)
  | .u1, x => Pi.single 1 (-x 4)
  | .u2, x => Pi.single 2 (-x 5)
  | .u3, x => Pi.single 3 (-x 6)
  | .v1, x => Pi.single 4 (-x 1)
  | .v2, x => Pi.single 5 (-x 2)
  | .v3, x => Pi.single 6 (-x 3)
  | .l12, _ => 0
  | .l13, _ => 0
  | .l21, _ => 0
  | .l23, _ => 0
  | .l31, _ => 0
  | .l32, _ => 0

/-- The coefficient of `r` in `x_α(r) x`. -/
def linCoeff (α : Root) (x : Fin 8 → A) : Fin 8 → A :=
  rootFun α 1 x - x - quadCoeff α x

/-- `x_α(r) x = x + r · X_α x + r² · X_α^{(2)} x`. -/
theorem rootFun_eq_expand (α : Root) (r : A) (x : Fin 8 → A) :
    rootFun α r x = x + r • linCoeff α x + r ^ 2 • quadCoeff α x := by
  cases α <;> funext i <;> fin_cases i <;>
    simp [rootFun, linCoeff, quadCoeff, Matrix.vecHead, Matrix.vecTail] <;> ring

end Expansion

/-! ### Stable subspaces -/

section Stable

variable {k : Type u} [Field k]

/-- If all `x_α(r) w` lie in a subspace containing `w`, and the field has an element other than
`0` and `1`, then both coefficients of the expansion of `x_α(r) w` lie in the subspace. -/
theorem coeff_mem_of_rootFun_mem {W : Submodule k (Fin 8 → k)} {c : k} (hc0 : c ≠ 0)
    (hc1 : c ≠ 1) (α : Root) {w : Fin 8 → k} (hw : w ∈ W) (h : ∀ r : k, rootFun α r w ∈ W) :
    linCoeff α w ∈ W ∧ quadCoeff α w ∈ W := by
  have h1 := h 1
  have hc := h c
  rw [rootFun_eq_expand] at h1 hc
  rw [one_smul, one_pow, one_smul] at h1
  have hab : linCoeff α w + quadCoeff α w ∈ W := by
    have := W.sub_mem h1 hw
    rwa [add_assoc, add_sub_cancel_left] at this
  have hab' : c • linCoeff α w + c ^ 2 • quadCoeff α w ∈ W := by
    have := W.sub_mem hc hw
    rwa [add_assoc, add_sub_cancel_left] at this
  have hb : (c - c ^ 2) • quadCoeff α w ∈ W := by
    have := W.sub_mem (W.smul_mem c hab) hab'
    convert this using 1
    module
  have hne : c - c ^ 2 ≠ 0 := by
    rw [show c - c ^ 2 = c * (1 - c) by ring]
    exact mul_ne_zero hc0 (sub_ne_zero.2 (Ne.symm hc1))
  have hq := (W.smul_mem_iff hne).1 hb
  refine ⟨?_, hq⟩
  have := W.sub_mem hab hq
  rwa [add_sub_cancel_right] at this

theorem single_one_mem_of_ne_zero {W : Submodule k (Fin 8 → k)} {j : Fin 8} {a : k} (ha : a ≠ 0)
    (h : (Pi.single j a : Fin 8 → k) ∈ W) : (Pi.single j 1 : Fin 8 → k) ∈ W := by
  have e : (Pi.single j a : Fin 8 → k) = a • (Pi.single j 1 : Fin 8 → k) := by
    funext i
    by_cases hi : i = j
    · subst hi
      simp
    · simp [hi]
  rw [e] at h
  exact (W.smul_mem_iff ha).1 h

/-- Stable subspaces containing a vector off the line of the unit contain `u₁, …, v₃`. -/
theorem stableSubspace : StableSubspaceStatement.{u} := by
  classical
  intro k _ _ W hroot _ hex
  obtain ⟨w, hwW, hwU⟩ := hex
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset k)
  have hc0 : c ≠ 0 := fun h => hc (by simp [h])
  have hc1 : c ≠ 1 := fun h => hc (by simp [h])
  have hst : ∀ (α : Root), ∀ v ∈ W, linCoeff α v ∈ W ∧ quadCoeff α v ∈ W :=
    fun α v hv => coeff_mem_of_rootFun_mem hc0 hc1 α hv
      (fun r => by rw [← rootMatrix_mulVec]; exact hroot α r v hv)
  have hneg : (-1 : k) ≠ 0 := neg_ne_zero.2 one_ne_zero
  -- moving between the basis vectors
  have l21 : linCoeff .l21 (Pi.single 1 1 : Fin 8 → k) = Pi.single 2 1 := by
    funext i; fin_cases i <;> simp [linCoeff, quadCoeff, rootFun, Matrix.vecHead, Matrix.vecTail]
  have l31 : linCoeff .l31 (Pi.single 1 1 : Fin 8 → k) = Pi.single 3 1 := by
    funext i; fin_cases i <;> simp [linCoeff, quadCoeff, rootFun, Matrix.vecHead, Matrix.vecTail]
  have l12 : linCoeff .l12 (Pi.single 2 1 : Fin 8 → k) = Pi.single 1 1 := by
    funext i; fin_cases i <;> simp [linCoeff, quadCoeff, rootFun, Matrix.vecHead, Matrix.vecTail]
  have l13 : linCoeff .l13 (Pi.single 3 1 : Fin 8 → k) = Pi.single 1 1 := by
    funext i; fin_cases i <;> simp [linCoeff, quadCoeff, rootFun, Matrix.vecHead, Matrix.vecTail]
  have q : ∀ (α : Root) (j : Fin 8) (v : Fin 8 → k) (a : k), v ∈ W → a ≠ 0 →
      quadCoeff α v = Pi.single j a → (Pi.single j 1 : Fin 8 → k) ∈ W := by
    intro α j v a hv ha he
    have := (hst α v hv).2
    rw [he] at this
    exact single_one_mem_of_ne_zero ha this
  have hall : (Pi.single 1 1 : Fin 8 → k) ∈ W →
      ∀ i : Fin 8, i ≠ 0 → i ≠ 7 → (Pi.single i 1 : Fin 8 → k) ∈ W := by
    intro h1 i hi0 hi7
    have h2 : (Pi.single 2 1 : Fin 8 → k) ∈ W := l21 ▸ (hst .l21 _ h1).1
    have h3 : (Pi.single 3 1 : Fin 8 → k) ∈ W := l31 ▸ (hst .l31 _ h1).1
    fin_cases i
    · exact absurd rfl hi0
    · exact h1
    · exact h2
    · exact h3
    · exact q .v1 4 _ (-1) h1 hneg (by simp [quadCoeff])
    · exact q .v2 5 _ (-1) h2 hneg (by simp [quadCoeff])
    · exact q .v3 6 _ (-1) h3 hneg (by simp [quadCoeff])
    · exact absurd rfl hi7
  have h1 : (Pi.single 1 1 : Fin 8 → k) ∈ W := by
    have of2 : (Pi.single 2 1 : Fin 8 → k) ∈ W → (Pi.single 1 1 : Fin 8 → k) ∈ W :=
      fun h => l12 ▸ (hst .l12 _ h).1
    have of3 : (Pi.single 3 1 : Fin 8 → k) ∈ W → (Pi.single 1 1 : Fin 8 → k) ∈ W :=
      fun h => l13 ▸ (hst .l13 _ h).1
    by_cases w4 : w 4 ≠ 0
    · exact q .u1 1 w (-w 4) hwW (neg_ne_zero.2 w4) rfl
    by_cases w5 : w 5 ≠ 0
    · exact of2 (q .u2 2 w (-w 5) hwW (neg_ne_zero.2 w5) rfl)
    by_cases w6 : w 6 ≠ 0
    · exact of3 (q .u3 3 w (-w 6) hwW (neg_ne_zero.2 w6) rfl)
    by_cases w1 : w 1 ≠ 0
    · have h4 := q .v1 4 w (-w 1) hwW (neg_ne_zero.2 w1) rfl
      exact q .u1 1 _ (-1) h4 hneg (by simp [quadCoeff])
    by_cases w2 : w 2 ≠ 0
    · have h5 := q .v2 5 w (-w 2) hwW (neg_ne_zero.2 w2) rfl
      exact of2 (q .u2 2 _ (-1) h5 hneg (by simp [quadCoeff]))
    by_cases w3 : w 3 ≠ 0
    · have h6 := q .v3 6 w (-w 3) hwW (neg_ne_zero.2 w3) rfl
      exact of3 (q .u3 3 _ (-1) h6 hneg (by simp [quadCoeff]))
    push Not at w1 w2 w3 w4 w5 w6
    have h07 : w 0 - w 7 ≠ 0 := by
      intro h
      apply hwU
      have : w = w 0 • unit k := by
        funext i
        fin_cases i <;> simp [unit, w1, w2, w3, w4, w5, w6, sub_eq_zero.1 h]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    have hl : linCoeff .u1 w = Pi.single 1 (w 0 - w 7) := by
      funext i
      fin_cases i <;>
        simp [linCoeff, quadCoeff, rootFun, w1, w2, w3, w4, w5, w6, Matrix.vecHead, Matrix.vecTail]
    have := (hst .u1 w hwW).1
    rw [hl] at this
    exact single_one_mem_of_ne_zero h07 this
  exact hall h1

end Stable

/-! ### Rigidity modulo the unit -/

section Rigidity

/-- An automorphism matrix moving each of `u₁, …, v₃` only by a multiple of the unit is the
identity. -/
theorem unitRigidity : UnitRigidityStatement.{u} := by
  intro A _ g hg hc
  obtain ⟨hu, hm⟩ := hg
  obtain ⟨c1, h1⟩ := hc 1 (by decide) (by decide)
  obtain ⟨c2, h2⟩ := hc 2 (by decide) (by decide)
  obtain ⟨c3, h3⟩ := hc 3 (by decide) (by decide)
  obtain ⟨c4, h4⟩ := hc 4 (by decide) (by decide)
  obtain ⟨c5, h5⟩ := hc 5 (by decide) (by decide)
  obtain ⟨c6, h6⟩ := hc 6 (by decide) (by decide)
  have m14 : mulFun A (Pi.single 1 1) (Pi.single 4 1) = Pi.single 0 1 := by
    funext i; fin_cases i <;> simp [mulFun]
  have m25 : mulFun A (Pi.single 2 1) (Pi.single 5 1) = Pi.single 0 1 := by
    funext i; fin_cases i <;> simp [mulFun]
  have m36 : mulFun A (Pi.single 3 1) (Pi.single 6 1) = Pi.single 0 1 := by
    funext i; fin_cases i <;> simp [mulFun]
  have k14 := hm (Pi.single 1 1) (Pi.single 4 1)
  have k25 := hm (Pi.single 2 1) (Pi.single 5 1)
  have k36 := hm (Pi.single 3 1) (Pi.single 6 1)
  rw [m14, h1, h4] at k14
  rw [m25, h2, h5] at k25
  rw [m36, h3, h6] at k36
  have a := k14.symm.trans k25
  have b := k14.symm.trans k36
  have a1 := congrFun a 1
  have a2 := congrFun a 2
  have a4 := congrFun a 4
  have a5 := congrFun a 5
  have b3 := congrFun b 3
  have b6 := congrFun b 6
  simp [mulFun, unit] at a1 a2 a4 a5 b3 b6
  subst a1 a2 a4 a5 b3 b6
  simp only [zero_smul, add_zero] at h1 h2 h3 h4 h5 h6 k14
  have e0 : g *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    rw [k14, m14]
  have e7 : g *ᵥ Pi.single 7 1 = Pi.single 7 1 := by
    have hs : (Pi.single 7 1 : Fin 8 → A) = unit A - Pi.single 0 1 := by
      funext i; fin_cases i <;> simp [unit]
    rw [hs, Matrix.mulVec_sub, hu, e0]
  have hcol : ∀ j : Fin 8, g *ᵥ Pi.single j 1 = Pi.single j 1 := by
    intro j
    fin_cases j
    · exact e0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact e7
  ext i j
  have := congrFun (hcol j) i
  rw [Matrix.mulVec_single_one] at this
  simpa [Matrix.one_apply, Pi.single_apply] using this

end Rigidity

/-! ### The quotient by the line of the unit -/

section Quotient

variable (A : Type u) [CommRing A]

/-- The projection `x ↦ (x₁, …, x₆, x₇ - x₀)` from `A⁸` to `A⁷`, with kernel the line of the
unit. -/
def projLin : (Fin 8 → A) →ₗ[A] (Fin 7 → A) where
  toFun x j := x j.succ - if j = 6 then x 0 else 0
  map_add' x y := by
    funext j
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c x := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

/-- The section `y ↦ (0, y₁, …, y₇)` of `projLin`. -/
def sectLin : (Fin 7 → A) →ₗ[A] (Fin 8 → A) where
  toFun y := Fin.cons 0 y
  map_add' y y' := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' c y := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

variable {A}

theorem projLin_apply (x : Fin 8 → A) (j : Fin 7) :
    projLin A x j = x j.succ - if j = 6 then x 0 else 0 := rfl

theorem projLin_sectLin (y : Fin 7 → A) : projLin A (sectLin A y) = y := by
  funext j
  simp [projLin_apply, sectLin]

theorem sectLin_projLin (x : Fin 8 → A) : sectLin A (projLin A x) = x - x 0 • unit A := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [sectLin, unit]
  · simp only [sectLin, LinearMap.coe_mk, AddHom.coe_mk, Fin.cons_succ, projLin_apply,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    fin_cases j <;> simp [unit]

theorem projLin_unit : projLin A (unit A) = 0 := by
  funext j
  fin_cases j <;> simp [projLin_apply, unit]

theorem eq_smul_unit_of_projLin_eq_zero {x : Fin 8 → A} (h : projLin A x = 0) :
    x = x 0 • unit A := by
  have := sectLin_projLin x
  rw [h, map_zero] at this
  exact (sub_eq_zero.1 this.symm)

theorem projLin_map {B : Type u} [CommRing B] (f : A →+* B) (x : Fin 8 → A) :
    (fun j => f (projLin A x j)) = projLin B (fun i => f (x i)) := by
  funext j
  simp only [projLin_apply]
  split_ifs <;> simp

variable (A) in
/-- The matrix of `projLin`. -/
def projMat : Matrix (Fin 7) (Fin 8) A := LinearMap.toMatrix' (projLin A)

variable (A) in
/-- The matrix of `sectLin`. -/
def sectMat : Matrix (Fin 8) (Fin 7) A := LinearMap.toMatrix' (sectLin A)

/-- The matrix induced on the quotient of `A⁸` by the line of the unit. -/
def quotMatrix (g : Matrix (Fin 8) (Fin 8) A) : Matrix (Fin 7) (Fin 7) A :=
  projMat A * g * sectMat A

theorem quotMatrix_mulVec (g : Matrix (Fin 8) (Fin 8) A) (y : Fin 7 → A) :
    quotMatrix g *ᵥ y = projLin A (g *ᵥ sectLin A y) := by
  rw [quotMatrix, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, projMat, sectMat,
    LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]

theorem quotMatrix_mulVec_projLin {g : Matrix (Fin 8) (Fin 8) A} (hg : g *ᵥ unit A = unit A)
    (x : Fin 8 → A) : quotMatrix g *ᵥ projLin A x = projLin A (g *ᵥ x) := by
  rw [quotMatrix_mulVec, sectLin_projLin, Matrix.mulVec_sub, Matrix.mulVec_smul, hg, map_sub,
    map_smul, projLin_unit, smul_zero, sub_zero]

theorem quotMatrix_eq_of_mulVec {M N : Matrix (Fin 7) (Fin 7) A} (h : ∀ y, M *ᵥ y = N *ᵥ y) :
    M = N :=
  Matrix.toLin'.injective (LinearMap.ext fun y => by simp only [Matrix.toLin'_apply]; exact h y)

theorem quotMatrix_mul {g : Matrix (Fin 8) (Fin 8) A} (hg : g *ᵥ unit A = unit A)
    (h : Matrix (Fin 8) (Fin 8) A) : quotMatrix (g * h) = quotMatrix g * quotMatrix h := by
  apply quotMatrix_eq_of_mulVec
  intro y
  rw [← Matrix.mulVec_mulVec, quotMatrix_mulVec h, quotMatrix_mulVec_projLin hg,
    quotMatrix_mulVec, Matrix.mulVec_mulVec]

theorem quotMatrix_one : quotMatrix (1 : Matrix (Fin 8) (Fin 8) A) = 1 := by
  apply quotMatrix_eq_of_mulVec
  intro y
  rw [quotMatrix_mulVec, Matrix.one_mulVec, Matrix.one_mulVec, projLin_sectLin]

theorem projMat_map {B : Type u} [CommRing B] (f : A →+* B) : (projMat A).map f = projMat B := by
  ext j i
  simp only [Matrix.map_apply, projMat, LinearMap.toMatrix'_apply, projLin_apply]
  split_ifs <;> simp [Pi.single_apply, apply_ite f]

theorem sectMat_map {B : Type u} [CommRing B] (f : A →+* B) : (sectMat A).map f = sectMat B := by
  ext i j
  simp only [Matrix.map_apply, sectMat, LinearMap.toMatrix'_apply]
  refine Fin.cases ?_ (fun l => ?_) i
  · simp [sectLin]
  · simp only [sectLin, LinearMap.coe_mk, AddHom.coe_mk, Fin.cons_succ]
    simp [Pi.single_apply, apply_ite f]

theorem quotMatrix_map {B : Type u} [CommRing B] (f : A →+* B) (g : Matrix (Fin 8) (Fin 8) A) :
    (quotMatrix g).map f = quotMatrix (g.map f) := by
  rw [quotMatrix, quotMatrix, Matrix.map_mul, Matrix.map_mul, projMat_map, sectMat_map]

end Quotient

end SplitCayley

end Langlands.GroupScheme
