import Langlands.Group.Unitary.Hyperbolic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.Group
import Mathlib.Tactic.Abel

/-!
# The big cell of `U(ν, ν)`

Let `E / F` be a quadratic extension with involution `c` (`IsQuadraticInvolution c δ`), `P` the
Siegel parabolic subgroup of `U(ν, ν)` and `w` the Weyl element
(`Langlands/Group/Unitary/Hyperbolic.lean`).

- `isInBigCell_iff_det_ne_zero`: `g ∈ P w P` exactly when the lower left block of `g` is invertible.
- `exists_mul_isInBigCell`: when `F` is infinite, every finite subset of `U(ν, ν)` has a common
  right translate into `P w P`. For one element `g = [[A, B], [C, D]]`, a Hermitian `t` with
  `C + D t` invertible is found by an induction on the dimension of the kernel of `C`, adding
  rank-one Hermitian corrections (the internal lemmas `transv_*`); for finitely many elements,
  `C + D (t₀ + r (t₁ - t₀))` is singular for only finitely many `r ∈ F`, since its determinant is
  a non-zero polynomial in `r`.
- `eq_top_of_siegelParabolic_le_of_weylElement_mem`: `P` and `w` generate `U(ν, ν)`.
- `isOpen_of_eventually_mem_siegelParabolic`: for `E` a Hausdorff topological field, a subgroup of
  `U(ν, ν)` containing a neighbourhood of `1` in `P` and in `w⁻¹ P w` is open (every element near
  `1` factors as an element of `P` near `1` times an element of `w⁻¹ P w` near `1`).

These are the group-theoretic inputs of the construction of the Leray splitting of `U(ν, ν)`
(`Langlands/Group/BigCellHom.lean`, `Langlands/Theta/DualPair/Unitary/Splitting.lean`).
-/

noncomputable section

open Matrix Filter Topology

namespace Langlands

namespace UnitaryGroup

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {ν : Type*} [Fintype ν] [DecidableEq ν]

namespace BigCell.Internal

/-- The matrix of an element of `U(ν, ν)`. -/
abbrev mat (g : ofForm c (hyperbolicForm ν E)) : Matrix (ν ⊕ ν) (ν ⊕ ν) E :=
  ((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E)

end BigCell.Internal

open BigCell.Internal

/-- **The big cell.** An element of `U(ν, ν)` lies in `P w P` exactly when its lower left block is
invertible. -/
theorem isInBigCell_iff_det_ne_zero (g : ofForm c (hyperbolicForm ν E)) :
    IsInBigCell c g ↔ (((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E).toBlocks₂₁).det ≠ 0 := by
  change IsInBigCell c g ↔ ((mat c g).toBlocks₂₁).det ≠ 0
  constructor
  · rintro ⟨p, hp, q, hq, rfl⟩
    have hdet : ∀ x : ofForm c (hyperbolicForm ν E), (mat c x).det ≠ 0 := fun x =>
      ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit (x : GL (ν ⊕ ν) E))).ne_zero
    have hp0 : mat c p = fromBlocks (mat c p).toBlocks₁₁ (mat c p).toBlocks₁₂ 0
        (mat c p).toBlocks₂₂ := by
      rw [← (mem_siegelParabolic c).1 hp, fromBlocks_toBlocks]
    have hq0 : mat c q = fromBlocks (mat c q).toBlocks₁₁ (mat c q).toBlocks₁₂ 0
        (mat c q).toBlocks₂₂ := by
      rw [← (mem_siegelParabolic c).1 hq, fromBlocks_toBlocks]
    have hpd := hdet p
    have hqd := hdet q
    rw [hp0, det_fromBlocks_zero₂₁] at hpd
    rw [hq0, det_fromBlocks_zero₂₁] at hqd
    change (mat c p * hyperbolicForm ν E * mat c q).toBlocks₂₁.det ≠ 0
    rw [hp0, hq0]
    simp only [hyperbolicForm_eq_fromBlocks, fromBlocks_multiply, toBlocks_fromBlocks₂₁]
    simp
    rw [det_neg, det_mul]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))
      (mul_ne_zero (right_ne_zero_of_mul hpd) (left_ne_zero_of_mul hqd))
  · intro hC
    set A := (mat c g).toBlocks₁₁ with hA
    set B := (mat c g).toBlocks₁₂ with hB
    set C := (mat c g).toBlocks₂₁ with hCdef
    set D := (mat c g).toBlocks₂₂ with hD
    have hg0 : mat c g = fromBlocks A B C D := (fromBlocks_toBlocks _).symm
    have hrel : mat c g * hyperbolicForm ν E * ((mat c g).map c)ᵀ = hyperbolicForm ν E :=
        (mem_ofForm_hyperbolicForm_iff c _).mp g.2
    have hkey : C * (D.map c)ᵀ = D * (C.map c)ᵀ := by
      have h := congrArg Matrix.toBlocks₂₂ hrel
      rw [hg0] at h
      simp only [hyperbolicForm_eq_fromBlocks, fromBlocks_map, fromBlocks_transpose,
          fromBlocks_multiply, toBlocks_fromBlocks₂₂] at h
      simp at h
      exact (neg_add_eq_zero.1 h).symm
    have hCu : IsUnit C := (Matrix.isUnit_iff_isUnit_det C).2 (isUnit_iff_ne_zero.2 hC)
    have hCs : IsUnit (C.map c)ᵀ := by
      rw [Matrix.isUnit_iff_isUnit_det, det_transpose]
      exact (hCu.map (RingHom.mapMatrix (c : E →+* E))).map detMonoidHom
    have hCC : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv C (isUnit_iff_ne_zero.2 hC)
    set v := C⁻¹ * D with hv
    have hvh : (v.map c)ᵀ = v := by
      apply hCu.mul_left_cancel
      apply hCs.mul_right_cancel
      have e1 : ((v.map c)ᵀ) * (C.map c)ᵀ = (D.map c)ᵀ := by
        rw [hv, Matrix.map_mul, transpose_mul, Matrix.mul_assoc, ← transpose_mul, ← Matrix.map_mul,
            hCC,
          Matrix.map_one _ (map_zero c) (map_one c), transpose_one, Matrix.mul_one]
      rw [Matrix.mul_assoc, e1, hkey, hv, ← Matrix.mul_assoc, hCC, Matrix.one_mul]
    let q := siegelUnipotent c v hvh
    have hq : q ∈ siegelParabolic c ν := by
      change (fromBlocks (1 : Matrix ν ν E) v 0 1).toBlocks₂₁ = 0
      rw [toBlocks_fromBlocks₂₁]
    refine ⟨g * q⁻¹ * (weylElement c ν)⁻¹, ?_, q, hq, by group⟩
    rw [mem_siegelParabolic c]
    change (mat c g * fromBlocks 1 (-v) 0 1 * -hyperbolicForm ν E).toBlocks₂₁ = 0
    rw [hg0]
    simp only [hyperbolicForm_eq_fromBlocks, fromBlocks_neg, fromBlocks_multiply,
        toBlocks_fromBlocks₂₁]
    simp
    rw [hv, ← Matrix.mul_assoc, hCC, Matrix.one_mul, neg_add_cancel]


namespace BigCell.Internal

section Transverse

variable {k : Type*} [Field k]

omit [DecidableEq ν] in
theorem transv_kills (c : k →+* k) (S A C : Matrix ν ν k)
    (hiso : Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0)
    (u : ν → k) (hu : A *ᵥ u = 0) (w : ν → k) :
    ((C *ᵥ u) ᵥ* S) ⬝ᵥ (c ∘ (A *ᵥ w)) = 0 := by
  have h := congrArg (fun M => u ⬝ᵥ (M *ᵥ (c ∘ w))) hiso
  simp only [add_mulVec, dotProduct_add, dotProduct_mulVec, zero_mulVec, dotProduct_zero] at h
  have e1 : u ᵥ* (Aᵀ * S * C.map c) = 0 := by
    rw [← vecMul_vecMul, ← vecMul_vecMul, vecMul_transpose, hu, zero_vecMul, zero_vecMul]
  have e2 : u ᵥ* (Cᵀ * S * A.map c) ⬝ᵥ (c ∘ w) = ((C *ᵥ u) ᵥ* S) ⬝ᵥ (c ∘ (A *ᵥ w)) := by
    rw [← vecMul_vecMul, ← dotProduct_mulVec, ← vecMul_vecMul, vecMul_transpose]
    congr 1
    funext i
    exact (RingHom.map_mulVec c A w i).symm
  rw [e1, zero_dotProduct, zero_add, e2] at h
  exact h

def transvRankOne (S : Matrix ν ν k) (j : ν) : Matrix ν ν k :=
  Matrix.of fun a b => if a = j then S b j else 0

theorem transvRankOne_adm (c : k →+* k) (S : Matrix ν ν k) (hS : Sᵀ = -S.map c) (j : ν) :
    (transvRankOne S j)ᵀ * S + S * (transvRankOne S j).map c = 0 := by
  ext a b
  have h1 : c (S b j) = - S j b := by
    have h2 : Sᵀ b j = (-S.map c) b j := by rw [hS]
    rw [transpose_apply, Matrix.neg_apply, Matrix.map_apply] at h2
    rw [h2, neg_neg]
  have h3 : ∀ l, c (if l = j then S b j else 0) = if l = j then c (S b j) else 0 := by
    intro l; split_ifs <;> simp
  simp [Matrix.mul_apply, transvRankOne, h3, h1]

theorem transvRankOne_mulVec (S : Matrix ν ν k) (j : ν) (v : ν → k) :
    transvRankOne S j *ᵥ v = Pi.single j ((v ᵥ* S) j) := by
  funext a
  by_cases h : a = j
  · subst h; simp [transvRankOne, mulVec, vecMul, dotProduct, mul_comm]
  · simp [transvRankOne, mulVec, dotProduct, h]

theorem transv_step (c : k →+* k) (S : Matrix ν ν k) (hSu : IsUnit S.det) (A C : Matrix ν ν k)
    (hinj : ∀ u : ν → k, A *ᵥ u = 0 → C *ᵥ u = 0 → u = 0)
    (hiso : Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0)
    (u : ν → k) (hu0 : u ≠ 0) (hu : A *ᵥ u = 0) :
    ∃ j : ν, (∀ w, (A + transvRankOne S j * C) *ᵥ w = 0 → A *ᵥ w = 0) ∧
      (A + transvRankOne S j * C) *ᵥ u ≠ 0 := by
  have hx : C *ᵥ u ≠ 0 := fun h => hu0 (hinj u hu h)
  have hxS : (C *ᵥ u) ᵥ* S ≠ 0 := by
    intro h
    have hI : Function.Injective fun v : ν → k => v ᵥ* S :=
      vecMul_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det S).mpr hSu)
    apply hx
    apply hI
    simp only [h, zero_vecMul]
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hxS
  simp only [Pi.zero_apply] at hj
  refine ⟨j, ?_, ?_⟩
  · intro w hw
    rw [add_mulVec, ← mulVec_mulVec, transvRankOne_mulVec] at hw
    set t := ((C *ᵥ w) ᵥ* S) j with ht
    have hAw : A *ᵥ w = - Pi.single j t := eq_neg_of_add_eq_zero_left hw
    have hφ := transv_kills c S A C hiso u hu w
    have hc : (c ∘ (A *ᵥ w)) = Pi.single j (-(c t)) := by
      rw [hAw]
      funext i
      by_cases hi : i = j
      · subst hi; simp
      · simp [hi]
    rw [hc, dotProduct_single] at hφ
    have hct : c t = 0 := by
      rcases mul_eq_zero.mp hφ with h | h
      · exact absurd h hj
      · exact neg_eq_zero.mp h
    have ht0 : t = 0 := (map_eq_zero c).mp hct
    rw [hAw, ht0, Pi.single_zero, neg_zero]
  · rw [add_mulVec, ← mulVec_mulVec, transvRankOne_mulVec, hu, zero_add]
    intro h
    have := congrFun h j
    simp only [Pi.single_eq_same, Pi.zero_apply] at this
    exact hj this

omit [DecidableEq ν] in
theorem transv_iso_update (c : k →+* k) (S A C X : Matrix ν ν k)
    (hX : Xᵀ * S + S * X.map c = 0)
    (hiso : Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0) :
    (A + X * C)ᵀ * S * C.map c + Cᵀ * S * (A + X * C).map c = 0 := by
  have e : (A + X * C)ᵀ * S * C.map c + Cᵀ * S * (A + X * C).map c =
      (Aᵀ * S * C.map c + Cᵀ * S * A.map c) + Cᵀ * (Xᵀ * S + S * X.map c) * C.map c := by
    rw [Matrix.map_add c (map_add c)]
    simp only [transpose_add, transpose_mul, Matrix.map_mul, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_assoc]
    abel
  rw [e, hiso, hX, Matrix.mul_zero, Matrix.zero_mul, add_zero]

omit [DecidableEq ν] in
theorem skewAdmissibleMatrix_add (c : k →+* k) (S X Y : Matrix ν ν k)
    (hX : Xᵀ * S + S * X.map c = 0) (hY : Yᵀ * S + S * Y.map c = 0) :
    (X + Y)ᵀ * S + S * (X + Y).map c = 0 := by
  have e : (X + Y)ᵀ * S + S * (X + Y).map c = (Xᵀ * S + S * X.map c) + (Yᵀ * S + S * Y.map c) := by
    rw [Matrix.map_add c (map_add c)]
    simp only [transpose_add, Matrix.mul_add, Matrix.add_mul]
    abel
  rw [e, hX, hY, add_zero]

theorem transv_field (c : k →+* k) (S : Matrix ν ν k) (hSu : IsUnit S.det) (hS : Sᵀ = -S.map c)
    (A C : Matrix ν ν k) (hinj : ∀ u : ν → k, A *ᵥ u = 0 → C *ᵥ u = 0 → u = 0)
    (hiso : Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0) :
    ∃ X : Matrix ν ν k, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det := by
  suffices H : ∀ m : ℕ, ∀ A : Matrix ν ν k,
      Module.finrank k (LinearMap.ker A.mulVecLin) < m →
      (∀ u : ν → k, A *ᵥ u = 0 → C *ᵥ u = 0 → u = 0) →
      Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0 →
      ∃ X : Matrix ν ν k, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det from
    H _ A (Nat.lt_succ_self _) hinj hiso
  intro m
  induction m with
  | zero => intro A h; exact absurd h (Nat.not_lt_zero _)
  | succ m ih =>
    intro A hm hinj hiso
    by_cases hdet : IsUnit A.det
    · exact ⟨0, by simp, by simpa using hdet⟩
    · have hd : A.det = 0 := by simpa [isUnit_iff_ne_zero] using hdet
      obtain ⟨u, hu0, hu⟩ := exists_mulVec_eq_zero_iff.mpr hd
      obtain ⟨j, hker, hne⟩ := transv_step c S hSu A C hinj hiso u hu0 hu
      have hX1 := transvRankOne_adm c S hS j
      have hlt : LinearMap.ker (A + transvRankOne S j * C).mulVecLin <
          LinearMap.ker A.mulVecLin := by
        refine lt_of_le_of_ne ?_ ?_
        · intro w hw
          simp only [LinearMap.mem_ker, mulVecLin_apply] at hw ⊢
          exact hker w hw
        · intro heq
          apply hne
          have hmem : u ∈ LinearMap.ker A.mulVecLin := by
            simpa [LinearMap.mem_ker, mulVecLin_apply] using hu
          rw [← heq] at hmem
          rw [LinearMap.mem_ker, mulVecLin_apply] at hmem
          exact hmem
      have hfin := Submodule.finrank_lt_finrank_of_lt hlt
      have hinj' : ∀ w : ν → k, (A + transvRankOne S j * C) *ᵥ w = 0 → C *ᵥ w = 0 → w = 0 := by
        intro w h1 h2
        apply hinj w _ h2
        rw [add_mulVec, ← mulVec_mulVec, h2, mulVec_zero, add_zero] at h1
        exact h1
      obtain ⟨X2, hX2, hdet2⟩ := ih (A + transvRankOne S j * C) (by omega) hinj'
        (transv_iso_update c S A C _ hX1 hiso)
      refine ⟨transvRankOne S j + X2, skewAdmissibleMatrix_add c S _ _ hX1 hX2, ?_⟩
      rwa [Matrix.add_mul, ← add_assoc]

end Transverse

variable {c} in
theorem exists_herm_transverse {δ : E} (hE : IsQuadraticInvolution c δ)
    (g : ofForm c (hyperbolicForm ν E)) :
    ∃ t : Matrix ν ν E,
        (t.map c)ᵀ = t ∧ ((mat c g).toBlocks₂₁ + (mat c g).toBlocks₂₂ * t).det ≠ 0 := by
  have hδ : δ ≠ 0 := hE.isUnit.ne_zero
  set M := mat c g with hMdef
  set cc := M.toBlocks₂₁
  set dd := M.toBlocks₂₂
  have hU := (mem_ofForm_hyperbolicForm_iff c _).mp g.2
  change M * hyperbolicForm ν E * (M.map c)ᵀ = hyperbolicForm ν E at hU
  have key : cc * (dd.map c)ᵀ = dd * (cc.map c)ᵀ := by
    have h := congrArg Matrix.toBlocks₂₂ hU
    rw [← fromBlocks_toBlocks M] at h
    simp only [hyperbolicForm_eq_fromBlocks, fromBlocks_map, fromBlocks_transpose,
        fromBlocks_multiply, toBlocks_fromBlocks₂₂] at h
    simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero,
        Matrix.neg_mul] at h
    have h' : cc * (dd.map c)ᵀ + -(dd * (cc.map c)ᵀ) = 0 := by rw [← h]; abel
    exact eq_of_sub_eq_zero (by rw [sub_eq_add_neg]; exact h')

  set S : Matrix ν ν E := δ • (1 : Matrix ν ν E)
  have hcδ : c δ = -δ := hE.map_eq_neg
  have hSu : IsUnit S.det := by
    rw [isUnit_iff_ne_zero]; simp [S, hδ]
  have hS : Sᵀ = -S.map (c : E →+* E) := by
    ext i j; by_cases h : i = j <;> simp [S, h, hcδ, eq_comm]
  have hmapC : (δ • ddᵀ).map (c : E →+* E) = (-δ) • (dd.map c)ᵀ := by
    ext i j; simp [hcδ]
  have hiso : (ccᵀ)ᵀ * S * (δ • ddᵀ).map (c : E →+* E) + (δ • ddᵀ)ᵀ * S * (ccᵀ).map
      (c : E →+* E) = 0 := by
    rw [hmapC]
    have e1 : (ccᵀ).map (c : E →+* E) = (cc.map c)ᵀ := rfl
    rw [e1]
    simp only [S, transpose_transpose, transpose_smul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, smul_smul, key]
    rw [← add_smul]; simp
  have hinj : ∀ u : ν → E, ccᵀ *ᵥ u = 0 → (δ • ddᵀ) *ᵥ u = 0 → u = 0 := by
    intro u h1 h2
    rw [mulVec_transpose] at h1
    rw [smul_mulVec, mulVec_transpose, smul_eq_zero] at h2
    have h2' : u ᵥ* dd = 0 := h2.resolve_left hδ
    have hw : (Sum.elim 0 u : ν ⊕ ν → E) ᵥ* M = 0 := by
      rw [← fromBlocks_toBlocks M]
      funext i
      rcases i with i | i
      · have := congrFun h1 i
        simpa [vecMul, dotProduct, fromBlocks, Fintype.sum_sum_type, cc] using this
      · have := congrFun h2' i
        simpa [vecMul, dotProduct, fromBlocks, Fintype.sum_sum_type, dd] using this
    have hinv : M * ((g⁻¹ : ofForm c (hyperbolicForm ν E)) : GL (ν ⊕ ν) E) = 1 := by
      change (((g * g⁻¹ : ofForm c (hyperbolicForm ν E)) : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν)
          (ν ⊕ ν) E) = 1
      rw [mul_inv_cancel]; rfl
    have hw0 : (Sum.elim 0 u : ν ⊕ ν → E) = 0 := by
      rw [← vecMul_one (Sum.elim 0 u : ν ⊕ ν → E), ← hinv, ← vecMul_vecMul, hw, zero_vecMul]
    funext i
    simpa using congrFun hw0 (Sum.inr i)
  obtain ⟨X, hX, hdet⟩ := transv_field (c : E →+* E) S hSu hS ccᵀ (δ • ddᵀ) hinj hiso
  refine ⟨δ • Xᵀ, ?_, ?_⟩
  · have hX' : δ • Xᵀ + δ • X.map (c : E →+* E) = 0 := by
      simpa [S, Matrix.mul_smul, Matrix.smul_mul] using hX
    rw [← smul_add, smul_eq_zero] at hX'
    have hX'' : X.map (c : E →+* E) = -Xᵀ := eq_neg_of_add_eq_zero_right (hX'.resolve_left hδ)
    have e : (δ • Xᵀ).map c = (-δ) • (X.map (c : E →+* E))ᵀ := by ext i j; simp [hcδ]
    rw [e, hX'']
    simp
  · have e : (ccᵀ + X * (δ • ddᵀ))ᵀ = cc + dd * (δ • Xᵀ) := by
      simp [transpose_add, transpose_mul]
    rw [← e, det_transpose]
    exact (isUnit_iff_ne_zero).mp hdet


theorem finite_det_line_zero (A B : Matrix ν ν E) (r₀ : F) (h :
    (A + algebraMap F E r₀ • B).det ≠ 0) :
    {r : F | (A + algebraMap F E r • B).det = 0}.Finite := by
  set M : Matrix ν ν (Polynomial E) := A.map Polynomial.C +
      (Polynomial.X : Polynomial E) • B.map Polynomial.C with hM
  have hev : ∀ x : E, M.det.eval x = (A + x • B).det := by
    intro x
    have h1 := RingHom.map_det (Polynomial.evalRingHom x) M
    rw [Polynomial.coe_evalRingHom] at h1
    rw [h1]
    congr 1
    ext i j
    simp [hM]
    ring
  have hp : M.det ≠ 0 := by
    intro h0
    apply h
    rw [← hev, h0, Polynomial.eval_zero]
  have hfin := Polynomial.finite_setOfPred_isRoot hp
  refine (hfin.preimage (f := algebraMap F E) (algebraMap F E).injective.injOn).subset ?_
  intro r hr
  change M.det.eval _ = 0
  rw [hev]
  exact hr

variable {c} in
theorem exists_herm_transversal [Infinite F] {δ : E} (hE : IsQuadraticInvolution c δ)
    (s : Finset (ofForm c (hyperbolicForm ν E))) :
    ∃ t : Matrix ν ν E, (t.map c)ᵀ = t ∧ ∀ g ∈ s,
        ((mat c g).toBlocks₂₁ + (mat c g).toBlocks₂₂ * t).det ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by ext i j; simp, by simp⟩
  | insert g s _ ih =>
    obtain ⟨t₀, ht₀, h₀⟩ := ih
    obtain ⟨t₁, ht₁, h₁⟩ := exists_herm_transverse hE g
    have key : ∀ k ∈ insert g s, {r : F | (((mat c k).toBlocks₂₁ + (mat c k).toBlocks₂₂ * t₀) +
        algebraMap F E r • ((mat c k).toBlocks₂₂ * (t₁ - t₀))).det = 0}.Finite := by
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · refine finite_det_line_zero _ _ 1 ?_
        rw [map_one, one_smul, add_assoc, ← Matrix.mul_add, add_sub_cancel]
        exact h₁
      · refine finite_det_line_zero _ _ 0 ?_
        rw [map_zero, zero_smul, add_zero]
        exact h₀ k hk
    have hfin := Set.Finite.biUnion (insert g s).finite_toSet key
    obtain ⟨r, hr⟩ := hfin.exists_notMem
    refine ⟨t₀ + algebraMap F E r • (t₁ - t₀), ?_, ?_⟩
    · ext i j
      have e₀ : c (t₀ j i) = t₀ i j := congrFun (congrFun ht₀ i) j
      have e₁ : c (t₁ j i) = t₁ i j := congrFun (congrFun ht₁ i) j
      simp [e₀, e₁]
    · intro k hk h0
      apply hr
      refine Set.mem_biUnion (Finset.mem_coe.mpr hk) ?_
      rw [Matrix.mul_add, Matrix.mul_smul, ← add_assoc] at h0
      exact h0

end BigCell.Internal

open BigCell.Internal

variable {c} in
/-- **Every finite set has a translate in the big cell.** -/
theorem exists_mul_isInBigCell [Infinite F] {δ : E} (hE : IsQuadraticInvolution c δ)
    (s : Finset (ofForm c (hyperbolicForm ν E))) :
    ∃ u : ofForm c (hyperbolicForm ν E), ∀ g ∈ s, IsInBigCell c (g * u) := by
  obtain ⟨t, ht, h⟩ := exists_herm_transversal hE s
  let u : ofForm c (hyperbolicForm ν E) :=
    ⟨⟨fromBlocks 1 0 t 1, fromBlocks 1 0 (-t) 1, by
        simp [fromBlocks_multiply], by simp [fromBlocks_multiply]⟩, by
      rw [mem_ofForm_hyperbolicForm_iff]
      have h0 : (0 : Matrix ν ν E).map c = 0 := Matrix.map_zero _ (map_zero c)
      have h1 : (1 : Matrix ν ν E).map c = 1 := Matrix.map_one _ (map_zero c) (map_one c)
      simp [hyperbolicForm_eq_fromBlocks, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply,
          h0, h1, ht]⟩
  refine ⟨u, fun g hg => (isInBigCell_iff_det_ne_zero c _).mpr ?_⟩
  have e : mat c (g * u) = mat c g * fromBlocks 1 0 t 1 := rfl
  change (mat c (g * u)).toBlocks₂₁.det ≠ 0
  rw [e, ← fromBlocks_toBlocks (mat c g), fromBlocks_multiply, toBlocks_fromBlocks₂₁,
      Matrix.mul_one]
  exact h g hg


theorem IsInBigCell.mem_of_le {U : Subgroup (ofForm c (hyperbolicForm ν E))}
    (hP : siegelParabolic c ν ≤ U) (hw : weylElement c ν ∈ U) {g : ofForm c (hyperbolicForm ν E)}
    (hg : IsInBigCell c g) : g ∈ U := by
  obtain ⟨p, hp, q, hq, rfl⟩ := hg
  exact U.mul_mem (U.mul_mem (hP hp) hw) (hP hq)

variable {c} in
/-- **The Siegel parabolic and the Weyl element generate `U(ν, ν)`.** -/
theorem eq_top_of_siegelParabolic_le_of_weylElement_mem [Infinite F] {δ : E}
    (hE : IsQuadraticInvolution c δ) {U : Subgroup (ofForm c (hyperbolicForm ν E))}
    (hP : siegelParabolic c ν ≤ U) (hw : weylElement c ν ∈ U) : U = ⊤ := by
  classical
  refine eq_top_iff.mpr fun g _ => ?_
  obtain ⟨u, hu⟩ := exists_mul_isInBigCell hE {1, g}
  have h1 : u ∈ U := by
    simpa using IsInBigCell.mem_of_le c hP hw (hu 1 (by simp))
  have h2 : g * u ∈ U := IsInBigCell.mem_of_le c hP hw (hu g (by simp))
  simpa using U.mul_mem h2 (U.inv_mem h1)


namespace BigCell.Internal

def vOf (g : ofForm c (hyperbolicForm ν E)) : Matrix ν ν E := (mat c g).toBlocks₂₂⁻¹ *
    (mat c g).toBlocks₂₁

theorem lower_rel (g : ofForm c (hyperbolicForm ν E)) :
    (mat c g).toBlocks₂₁ * ((mat c g).toBlocks₂₂.map c)ᵀ = (mat c g).toBlocks₂₂ *
        ((mat c g).toBlocks₂₁.map c)ᵀ := by
  have h : mat c g * hyperbolicForm ν E * ((mat c g).map c)ᵀ = hyperbolicForm ν E :=
      (mem_ofForm_hyperbolicForm_iff c _).mp g.2
  have h2 := congrArg Matrix.toBlocks₂₂ h
  rw [← fromBlocks_toBlocks (mat c g)] at h2
  simp [hyperbolicForm_eq_fromBlocks, fromBlocks_map, fromBlocks_transpose,
      fromBlocks_multiply] at h2
  rw [neg_add_eq_zero] at h2
  exact h2.symm

theorem vOf_herm (g : ofForm c (hyperbolicForm ν E)) (hd : IsUnit (mat c g).toBlocks₂₂.det) :
    ((-vOf c g).map c)ᵀ = -vOf c g := by
  set D := (mat c g).toBlocks₂₂ with hD
  set C := (mat c g).toBlocks₂₁ with hC
  have hrel : C * (D.map c)ᵀ = D * (C.map c)ᵀ := lower_rel c g
  have hdetc : ((D.map c)ᵀ).det = c D.det := by
    rw [det_transpose, show D.map c = (c : E →+* E).mapMatrix D from rfl, ← RingHom.map_det]; rfl
  have hDs : IsUnit ((D.map c)ᵀ).det := by rw [hdetc]; exact hd.map c
  have hV : vOf c g = D⁻¹ * C := rfl
  have hDV : D * vOf c g = C := by rw [hV, mul_nonsing_inv_cancel_left _ _ hd]
  have hstar : ((vOf c g).map c)ᵀ * (D.map c)ᵀ = (C.map c)ᵀ := by
    rw [← transpose_mul, ← hDV]
    exact congrArg Matrix.transpose (Matrix.map_mul (f := c.toRingHom) (L := D) (M := vOf c g)).symm
  have key : D * ((vOf c g).map c)ᵀ * (D.map c)ᵀ = D * vOf c g * (D.map c)ᵀ := by
    rw [Matrix.mul_assoc, hstar, hDV, hrel]
  have h3 : ((vOf c g).map c)ᵀ = vOf c g := by
    have := congrArg (fun X => D⁻¹ * X * ((D.map c)ᵀ)⁻¹) key
    simp only [Matrix.mul_assoc] at this
    rw [nonsing_inv_mul_cancel_left _ _ hd, nonsing_inv_mul_cancel_left _ _ hd,
        mul_nonsing_inv _ hDs, Matrix.mul_one,
      Matrix.mul_one] at this
    exact this
  rw [Matrix.map_neg _ (map_neg c), transpose_neg, h3]

open scoped Classical in

def nOf (g : ofForm c (hyperbolicForm ν E)) : ofForm c (hyperbolicForm ν E) :=
  if h : IsUnit (mat c g).toBlocks₂₂.det then siegelUnipotent c (-vOf c g) (vOf_herm c g h) else 1

def kOf (g : ofForm c (hyperbolicForm ν E)) : ofForm c (hyperbolicForm ν E) :=
    (weylElement c ν)⁻¹ * nOf c g * weylElement c ν

def pOf (g : ofForm c (hyperbolicForm ν E)) : ofForm c (hyperbolicForm ν E) := g * (kOf c g)⁻¹

theorem nOf_mem (g : ofForm c (hyperbolicForm ν E)) : nOf c g ∈ siegelParabolic c ν := by
  unfold nOf
  split_ifs with h
  · rw [mem_siegelParabolic c]
    change (fromBlocks 1 (-vOf c g) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E).toBlocks₂₁ = 0
    simp
  · exact (siegelParabolic c ν).one_mem

theorem pOf_mem (g : ofForm c (hyperbolicForm ν E)) (hd : IsUnit
    (mat c g).toBlocks₂₂.det) : pOf c g ∈ siegelParabolic c ν := by
  rw [mem_siegelParabolic c]
  have hk : mat c (pOf c g) = mat c g * (-hyperbolicForm ν E * (fromBlocks 1
      (-(-vOf c g)) 0 1 * hyperbolicForm ν E)) := by
    simp only [pOf, kOf, _root_.mul_inv_rev, inv_inv, nOf, dite_eq_left hd]
    rfl
  change (mat c (pOf c g)).toBlocks₂₁ = 0
  rw [hk]
  have hDV : (mat c g).toBlocks₂₂ * vOf c g =
      (mat c g).toBlocks₂₁ := mul_nonsing_inv_cancel_left _ _ hd
  set M := mat c g
  rw [← fromBlocks_toBlocks M]
  simp [hyperbolicForm_eq_fromBlocks, fromBlocks_multiply, fromBlocks_neg]
  rw [hDV, add_neg_cancel]

section Top

variable [TopologicalSpace E] [IsTopologicalRing E] [ContinuousInv₀ E] [T2Space E]

omit [IsTopologicalRing E] [ContinuousInv₀ E] [T2Space E] in
theorem continuous_mat : Continuous (mat c : ofForm c (hyperbolicForm ν E) → Matrix (ν ⊕ ν)
    (ν ⊕ ν) E) :=
  Units.continuous_val.comp continuous_subtype_val

omit [IsTopologicalRing E] [ContinuousInv₀ E] [T2Space E] in
theorem continuous_blk₂₂ : Continuous fun g : ofForm c (hyperbolicForm ν E) =>
    (mat c g).toBlocks₂₂ :=
  continuous_matrix fun _ _ => (continuous_mat c).matrix_elem _ _

omit [IsTopologicalRing E] [ContinuousInv₀ E] [T2Space E] in
theorem continuous_blk₂₁ : Continuous fun g : ofForm c (hyperbolicForm ν E) =>
    (mat c g).toBlocks₂₁ :=
  continuous_matrix fun _ _ => (continuous_mat c).matrix_elem _ _

omit [TopologicalSpace E] [IsTopologicalRing E] [ContinuousInv₀ E] [T2Space E] in
theorem blk₂₂_one : (mat c (1 : ofForm c (hyperbolicForm ν E))).toBlocks₂₂ = 1 := by
  ext i j; simp [mat, toBlocks₂₂, one_apply]

omit [TopologicalSpace E] [IsTopologicalRing E] [ContinuousInv₀ E] [T2Space E] in
theorem blk₂₁_one : (mat c (1 : ofForm c (hyperbolicForm ν E))).toBlocks₂₁ = 0 := by
  ext i j; simp [mat, toBlocks₂₁, one_apply]

omit [ContinuousInv₀ E] in
theorem eventually_isUnit : ∀ᶠ g in 𝓝 (1 : ofForm c (hyperbolicForm ν E)),
    IsUnit (mat c g).toBlocks₂₂.det := by
  have h : Tendsto (fun g : ofForm c (hyperbolicForm ν E) => (mat c g).toBlocks₂₂.det) (𝓝 1)
      (𝓝 1) := by
    have := ((continuous_blk₂₂ c).matrix_det).tendsto (1 : ofForm c (hyperbolicForm ν E))
    rwa [blk₂₂_one, det_one] at this
  filter_upwards [h.eventually_ne one_ne_zero] with g hg
  exact isUnit_iff_ne_zero.mpr hg

omit [T2Space E] in
theorem tendsto_vOf : Tendsto (vOf c) (𝓝 (1 : ofForm c (hyperbolicForm ν E))) (𝓝 0) := by
  have hinv : ContinuousAt (fun g : ofForm c (hyperbolicForm ν E) => (mat c g).toBlocks₂₂⁻¹) 1 := by
    refine ContinuousAt.comp (g := Inv.inv) ?_ (continuous_blk₂₂ c).continuousAt
    apply continuousAt_matrix_inv
    rw [Ring.inverse_eq_inv', blk₂₂_one, det_one]
    exact continuousAt_inv₀ one_ne_zero
  have h2 : Tendsto (vOf c) (𝓝 1) (𝓝 (vOf c 1)) := (hinv.mul
      (continuous_blk₂₁ c).continuousAt).tendsto
  have h0 : vOf c (1 : ofForm c (hyperbolicForm ν E)) = 0 := by rw [vOf, blk₂₁_one, Matrix.mul_zero]
  rwa [h0] at h2

theorem tendsto_nOf : Tendsto (nOf c) (𝓝 (1 : ofForm c (hyperbolicForm ν E))) (𝓝 1) := by
  rw [tendsto_subtype_rng, Units.isInducing_embedProduct.tendsto_nhds_iff]
  have hv := tendsto_vOf c (ν := ν)
  have hA : Tendsto (fun g => (fromBlocks 1 (-vOf c g) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E)) (𝓝 1)
      (𝓝 1) := by
    have hc : Continuous fun v : Matrix ν ν E => (fromBlocks 1 (-v) 0 1 : Matrix (ν ⊕ ν)
        (ν ⊕ ν) E) :=
      continuous_const.matrix_fromBlocks continuous_neg continuous_const continuous_const
    have := (hc.tendsto 0).comp hv
    rwa [neg_zero, fromBlocks_one] at this
  have hB : Tendsto (fun g => (fromBlocks 1 (-(-vOf c g)) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E)) (𝓝 1)
      (𝓝 1) := by
    have hc : Continuous fun v : Matrix ν ν E => (fromBlocks 1 (-(-v)) 0 1 : Matrix (ν ⊕ ν)
        (ν ⊕ ν) E) :=
      continuous_const.matrix_fromBlocks continuous_neg.neg continuous_const continuous_const
    have := (hc.tendsto 0).comp hv
    rwa [neg_zero, neg_zero, fromBlocks_one] at this
  have hE : (fun g => ((fromBlocks 1 (-vOf c g) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E),
      MulOpposite.op (fromBlocks 1 (-(-vOf c g)) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E))) =ᶠ[𝓝 1]
      (Units.embedProduct _ ∘ fun g => ((nOf c g : ofForm c (hyperbolicForm ν E)) : GL
          (ν ⊕ ν) E)) := by
    filter_upwards [eventually_isUnit c] with g hg
    simp only [Function.comp_apply, nOf, dite_eq_left hg]
    rfl
  refine Tendsto.congr' hE ?_
  have h1 : Units.embedProduct _ ((1 : ofForm c (hyperbolicForm ν E)) : GL (ν ⊕ ν) E) = (1,
      MulOpposite.op 1) := rfl
  rw [h1]
  exact hA.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp hB)

end Top

end BigCell.Internal

open BigCell.Internal in
/-- **An open-subgroup criterion.** For a Hausdorff topological field `E`, a subgroup of
`U(ν, ν)` which contains the elements near `1` of the Siegel parabolic `P` and the elements near
`1` of `w⁻¹ P w` is open. -/
theorem isOpen_of_eventually_mem_siegelParabolic [TopologicalSpace E] [IsTopologicalRing E]
    [ContinuousInv₀ E] [T2Space E] {U : Subgroup (ofForm c (hyperbolicForm ν E))}
    (h1 : ∀ᶠ g in 𝓝 (1 : ofForm c (hyperbolicForm ν E)), g ∈ siegelParabolic c ν → g ∈ U)
    (h2 : ∀ᶠ g in 𝓝 (1 : ofForm c (hyperbolicForm ν E)), g ∈ siegelParabolic c ν →
      (weylElement c ν)⁻¹ * g * weylElement c ν ∈ U) :
    IsOpen (U : Set (ofForm c (hyperbolicForm ν E))) := by
  refine Subgroup.isOpen_of_mem_nhds U (g := 1) ?_
  have hn : Tendsto (nOf c) (𝓝 (1 : ofForm c (hyperbolicForm ν E))) (𝓝 1) := tendsto_nOf c
  have hk : Tendsto (kOf c) (𝓝 (1 : ofForm c (hyperbolicForm ν E))) (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (weylElement c ν)⁻¹)).mul hn).mul (tendsto_const_nhds
        (x := weylElement c ν))
    rwa [mul_one, inv_mul_cancel] at this
  have hp : Tendsto (pOf c) (𝓝 (1 : ofForm c (hyperbolicForm ν E))) (𝓝 1) := by
    have := (tendsto_id (x := 𝓝 (1 : ofForm c (hyperbolicForm ν E)))).mul hk.inv
    rwa [inv_one, mul_one] at this
  filter_upwards [hp.eventually h1, hn.eventually h2, eventually_isUnit c] with g hpg hng hd
  have hg : g = pOf c g * kOf c g := by rw [pOf, inv_mul_cancel_right]
  rw [hg]
  exact U.mul_mem (hpg (pOf_mem c g hd)) (hng (nOf_mem c g))

end UnitaryGroup

end Langlands
