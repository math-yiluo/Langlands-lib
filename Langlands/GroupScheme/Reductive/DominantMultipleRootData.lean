import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Integral root-datum lemmas for positive multiples of dominant weights -/

noncomputable section

open Set Submodule

namespace Langlands.RootDatum.DominantMultiple

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] [Finite ι]
  (P : RootPairing ι ℤ M N) (b : P.Base)

omit [Finite ι] in
/-- The integral pairing of a nonnegative integral combination of simple roots. -/
theorem pairing_sum_nsmul (f : ι → ℕ) (x : N) :
    P.toLinearMap (∑ j ∈ b.support, f j • P.root j) x =
      ∑ j ∈ b.support, (f j : ℤ) * P.toLinearMap (P.root j) x := by
  simp [map_sum, LinearMap.sum_apply]

omit [Finite ι] in
/-- Every root is positive on a strictly dominant cocharacter and nonnegative on a dominant
one, or negative on the first and nonpositive on the second. -/
theorem root_sign (nu mu : N)
    (hnu : ∀ a ∈ b.support, 0 < P.toLinearMap (P.root a) nu)
    (hmu : ∀ a ∈ b.support, 0 ≤ P.toLinearMap (P.root a) mu) (r : ι) :
    (0 < P.toLinearMap (P.root r) nu ∧ 0 ≤ P.toLinearMap (P.root r) mu) ∨
      (P.toLinearMap (P.root r) nu < 0 ∧ P.toLinearMap (P.root r) mu ≤ 0) := by
  classical
  obtain ⟨f, -, hf⟩ := b.exists_root_eq_sum_nat_or_neg r
  have hne : ∃ j ∈ b.support, f j ≠ 0 := by
    by_contra h
    push Not at h
    have h0 : ∑ j ∈ b.support, f j • P.root j = 0 :=
      Finset.sum_eq_zero fun j hj => by rw [h j hj, zero_smul]
    rcases hf with hf | hf
    · exact P.ne_zero r (by rw [hf, h0])
    · exact P.ne_zero r (by rw [hf, h0, neg_zero])
  obtain ⟨j₀, hj₀, hf₀⟩ := hne
  have hpos : 0 < ∑ j ∈ b.support, (f j : ℤ) * P.toLinearMap (P.root j) nu := by
    refine Finset.sum_pos' (fun j hj => mul_nonneg (Int.natCast_nonneg _) (hnu j hj).le)
      ⟨j₀, hj₀, mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hf₀) (hnu j₀ hj₀)⟩
  have hnn : 0 ≤ ∑ j ∈ b.support, (f j : ℤ) * P.toLinearMap (P.root j) mu :=
    Finset.sum_nonneg fun j hj => mul_nonneg (Int.natCast_nonneg _) (hmu j hj)
  rcases hf with hf | hf
  · left
    rw [hf, pairing_sum_nsmul, pairing_sum_nsmul]
    exact ⟨hpos, hnn⟩
  · right
    simp only [hf, map_neg, LinearMap.neg_apply, pairing_sum_nsmul]
    exact ⟨neg_neg_of_pos hpos, neg_nonpos.mpr hnn⟩

omit [Finite ι] in
/-- A cocharacter killed by every simple root is killed by every root. -/
theorem pairing_root_eq_zero_of_simple (x : N)
    (hx : ∀ a ∈ b.support, P.toLinearMap (P.root a) x = 0) (r : ι) :
    P.toLinearMap (P.root r) x = 0 := by
  have key : ∀ y ∈ span ℤ (P.root '' b.support), P.toLinearMap y x = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      exact hx a ha
    | zero => simp
    | add y z _ _ hy hz => simp [hy, hz]
    | smul c y _ hy => simp [hy]
  exact key _ (b.root_mem_span_int r)

omit [Finite ι] in
/-- A character killed by every simple coroot is killed by every coroot. -/
theorem pairing_coroot_eq_zero_of_simple (x : M)
    (hx : ∀ a ∈ b.support, P.toLinearMap x (P.coroot a) = 0) (r : ι) :
    P.toLinearMap x (P.coroot r) = 0 := by
  have key : ∀ y ∈ span ℤ (P.coroot '' b.support), P.toLinearMap x y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      exact hx a ha
    | zero => simp
    | add y z _ _ hy hz => simp [hy, hz]
    | smul c y _ hy => simp [hy]
  exact key _ (b.coroot_mem_span_int r)

/-- An element of the integral coroot span killed by every simple root is zero. -/
theorem eq_zero_of_mem_corootSpan (x : N) (hxs : x ∈ P.corootSpan ℤ)
    (hx : ∀ a ∈ b.support, P.toLinearMap (P.root a) x = 0) : x = 0 := by
  have : Fintype ι := Fintype.ofFinite ι
  apply P.flip.eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero hxs
  change P.CorootForm x x = 0
  rw [P.corootForm_apply_apply]
  refine Finset.sum_eq_zero fun r _ => ?_
  change P.toLinearMap (P.root r) x * P.toLinearMap (P.root r) x = 0
  rw [pairing_root_eq_zero_of_simple P b x hx r, zero_mul]

/-- An element of the integral root span killed by every simple coroot is zero. -/
theorem eq_zero_of_mem_rootSpan (x : M) (hxs : x ∈ P.rootSpan ℤ)
    (hx : ∀ a ∈ b.support, P.toLinearMap x (P.coroot a) = 0) : x = 0 := by
  have : Fintype ι := Fintype.ofFinite ι
  apply P.eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero hxs
  rw [P.rootForm_apply_apply]
  refine Finset.sum_eq_zero fun r _ => ?_
  change P.toLinearMap x (P.coroot r) * P.toLinearMap x (P.coroot r) = 0
  rw [pairing_coroot_eq_zero_of_simple P b x hx r, zero_mul]

/-- The integral Cartan matrix of the simple roots against the simple coroots. -/
def cartan : Matrix b.support b.support ℤ :=
  Matrix.of fun j k => P.toLinearMap (P.root j) (P.coroot k)

open Classical in
theorem cartan_det_ne_zero : (cartan P b).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let x : N := ∑ k : b.support, v k • P.coroot k
  have hxs : x ∈ P.corootSpan ℤ :=
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (subset_span ⟨k, rfl⟩)
  have hx : ∀ a ∈ b.support, P.toLinearMap (P.root a) x = 0 := by
    intro a ha
    have h := congrFun hAv ⟨a, ha⟩
    simpa [x, cartan, Matrix.mulVec, dotProduct, map_sum, mul_comm] using h
  have hx0 := eq_zero_of_mem_corootSpan P b x hxs hx
  have hli : LinearIndependent ℤ (fun k : b.support => P.coroot k) :=
    b.linearIndepOn_coroot
  exact hv (funext fun k => by
    simpa using Fintype.linearIndependent_iff.mp hli v hx0 k)

/-- For each simple root there is an element of the integral coroot span pairing positively
with that simple root and trivially with all other simple roots. -/
theorem exists_simple_dual (i : b.support) :
    ∃ ν ∈ P.corootSpan ℤ, ∃ c : ℤ, 0 < c ∧ P.toLinearMap (P.root i) ν = c ∧
      ∀ a ∈ b.support, a ≠ i → P.toLinearMap (P.root a) ν = 0 := by
  classical
  let A := cartan P b
  let ν : N := A.det • ∑ k : b.support, A.adjugate k i • P.coroot k
  have hpair : ∀ a : b.support,
      P.toLinearMap (P.root a) ν = A.det * (A.det • (1 : Matrix b.support b.support ℤ)) a i := by
    intro a
    have h := congrFun (congrFun (Matrix.mul_adjugate A) a) i
    have hsum : P.toLinearMap (P.root a) (∑ k : b.support, A.adjugate k i • P.coroot k) =
        (A * A.adjugate) a i := by
      simp [Matrix.mul_apply, map_sum, A, cartan, mul_comm]
    rw [map_zsmul, hsum, h, smul_eq_mul]
  refine ⟨ν, ?_, A.det * A.det, mul_self_pos.mpr (cartan_det_ne_zero P b), ?_, ?_⟩
  · exact Submodule.smul_mem _ _
      (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (subset_span ⟨k, rfl⟩))
  · rw [hpair i]
    simp
  · intro a ha hai
    have hne : (⟨a, ha⟩ : b.support) ≠ i := fun h => hai (congrArg Subtype.val h)
    rw [hpair ⟨a, ha⟩]
    simp [Matrix.one_apply_ne hne]

omit [Finite ι] in
/-- The coroot form evaluated against a coroot is half its length times the root pairing. -/
theorem two_mul_corootForm_coroot [Fintype ι] (r : ι) (x : N) :
    2 * P.CorootForm (P.coroot r) x =
      P.CorootForm (P.coroot r) (P.coroot r) * P.toLinearMap (P.root r) x := by
  have h := congrArg (fun m => P.toLinearMap m x) (P.corootForm_self_smul_root r)
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, map_nsmul, LinearMap.smul_apply,
    P.toLinearMap_apply_CoPolarization, nsmul_eq_mul, Nat.cast_ofNat] at h
  exact h.symm

/-- Positivity of the simple-coroot pairing of a weight orthogonal to the other simple
coroots, detected by a positive pairing with a dual element of the coroot span. -/
theorem pairing_simple_coroot_pos (i : ι) (hi : i ∈ b.support) (ν : N)
    (hνs : ν ∈ P.corootSpan ℤ)
    (hν : ∀ a ∈ b.support, a ≠ i → P.toLinearMap (P.root a) ν = 0)
    (hνi : 0 < P.toLinearMap (P.root i) ν) (σ : M)
    (hσ : ∀ a ∈ b.support, a ≠ i → P.toLinearMap σ (P.coroot a) = 0)
    (hσν : 0 < P.toLinearMap σ ν) :
    0 < P.toLinearMap σ (P.coroot i) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have hνs' : ν ∈ span ℤ (P.coroot '' b.support) := by
    rw [b.span_int_coroot_support]
    exact hνs
  rw [Fintype.mem_span_image_iff_exists_fun] at hνs'
  obtain ⟨m, hm⟩ := hνs'
  let i' : ↥(b.support : Set ι) := ⟨i, hi⟩
  have hne : ∀ a : ↥(b.support : Set ι), a ≠ i' → (a : ι) ≠ i :=
    fun a ha h => ha (Subtype.ext h)
  have hσν' : P.toLinearMap σ ν = m i' * P.toLinearMap σ (P.coroot i) := by
    rw [← hm, map_sum, Finset.sum_eq_single i']
    · simp [i']
    · intro a _ ha
      simp [hσ a a.2 (hne a ha)]
    · simp
  have h1 : P.CorootForm ν ν = ∑ a, m a * P.CorootForm (P.coroot a) ν := by
    calc P.CorootForm ν ν = P.CorootForm (∑ a, m a • P.coroot a) ν := by rw [hm]
    _ = _ := by
      rw [map_sum, LinearMap.sum_apply]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  have hform : 2 * P.CorootForm ν ν =
      m i' * (P.CorootForm (P.coroot i) (P.coroot i) * P.toLinearMap (P.root i) ν) := by
    rw [h1, Finset.mul_sum, Finset.sum_eq_single i']
    · rw [mul_left_comm]
      exact congrArg (m i' * ·) (two_mul_corootForm_coroot P i ν)
    · intro a _ ha
      rw [mul_left_comm, two_mul_corootForm_coroot, hν a a.2 (hne a ha), mul_zero, mul_zero]
    · simp
  have hν0 : ν ≠ 0 := by
    rintro rfl
    simp at hνi
  have hνs'' : ν ∈ P.flip.rootSpan ℤ := hνs
  have hpos : 0 < P.CorootForm ν ν := P.flip.rootForm_pos_of_ne_zero hνs'' hν0
  have hlen : 0 < P.CorootForm (P.coroot i) (P.coroot i) := by
    have hs : P.coroot i ∈ P.flip.rootSpan ℤ := subset_span ⟨i, rfl⟩
    exact P.flip.rootForm_pos_of_ne_zero hs (P.ne_zero' i)
  have hmi : 0 < m i' := by
    by_contra h
    push Not at h
    have : 2 * P.CorootForm ν ν ≤ 0 := by
      rw [hform]
      exact mul_nonpos_of_nonpos_of_nonneg h (mul_pos hlen hνi).le
    linarith
  rw [hσν'] at hσν
  exact pos_of_mul_pos_right hσν hmi.le

omit [Finite ι] in
/-- If no nonzero cocharacter is orthogonal to a submodule of characters, then every
character has a positive multiple in that submodule. -/
theorem exists_pos_nsmul_mem_of_orthogonal [Module.Finite ℤ M] (L : Submodule ℤ M)
    (hL : ∀ n : N, (∀ l ∈ L, P.toLinearMap l n = 0) → n = 0) (x : M) :
    ∃ m : ℕ, 0 < m ∧ m • x ∈ L := by
  by_contra hcon
  push Not at hcon
  let q : M →ₗ[ℤ] M ⧸ L := L.mkQ
  let T := Submodule.torsion ℤ (M ⧸ L)
  have hx' : T.mkQ (q x) ≠ 0 := by
    intro h
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_torsion_iff] at h
    obtain ⟨⟨a, ha⟩, hax⟩ := h
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    have hax' : a • q x = 0 := hax
    have hmem : a • x ∈ L := by
      rw [← Submodule.Quotient.mk_eq_zero L, Submodule.Quotient.mk_smul]
      exact hax'
    have hmem' : (a.natAbs : ℤ) • x ∈ L := by
      rcases Int.natAbs_eq a with h | h
      · rw [← h]; exact hmem
      · rw [show (a.natAbs : ℤ) = -a by omega, neg_smul]
        exact L.neg_mem hmem
    exact hcon a.natAbs (Int.natAbs_pos.mpr ha0) (by rwa [natCast_zsmul] at hmem')
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero ℤ hx'
  let ψ : Module.Dual ℤ M := φ ∘ₗ T.mkQ ∘ₗ q
  let n : N := P.toLinearMap.flip.toPerfPair.symm ψ
  have hn : ∀ y : M, P.toLinearMap y n = ψ y := by
    intro y
    simp [n]
  have hn0 : n = 0 := hL n fun l hl => by
    rw [hn]
    simp [ψ, q, (Submodule.Quotient.mk_eq_zero L).mpr hl]
  apply hφ
  have := hn x
  rw [hn0, map_zero] at this
  simp [ψ] at this
  exact this.symm

omit [Finite ι] in
/-- The final integral combination: a dominant character has a positive multiple in any
additive submonoid containing suitable simple-direction weights and positive multiples of
every character orthogonal to the simple coroots. -/
theorem exists_pos_nsmul_mem_of_dominant (S : AddSubmonoid M) (σ : ι → M)
    (hσS : ∀ i ∈ b.support, σ i ∈ S)
    (hσ0 : ∀ i ∈ b.support, ∀ a ∈ b.support, a ≠ i → P.toLinearMap (σ i) (P.coroot a) = 0)
    (hσpos : ∀ i ∈ b.support, 0 < P.toLinearMap (σ i) (P.coroot i))
    (hX0 : ∀ x : M, (∀ a ∈ b.support, P.toLinearMap x (P.coroot a) = 0) →
      ∃ m : ℕ, 0 < m ∧ m • x ∈ S)
    (lam : M) (hlam : ∀ a ∈ b.support, 0 ≤ P.toLinearMap lam (P.coroot a)) :
    ∃ n : ℕ, 0 < n ∧ n • lam ∈ S := by
  classical
  let c : ι → ℤ := fun i => P.toLinearMap (σ i) (P.coroot i)
  let C : ℤ := ∏ i ∈ b.support, c i
  have hC : 0 < C := Finset.prod_pos fun i hi => hσpos i hi
  let a : ι → ℤ := fun i => P.toLinearMap lam (P.coroot i) * ∏ k ∈ b.support.erase i, c k
  have ha : ∀ i ∈ b.support, 0 ≤ a i := fun i hi =>
    mul_nonneg (hlam i hi) (Finset.prod_nonneg fun k hk =>
      (hσpos k (Finset.mem_of_mem_erase hk)).le)
  let y : M := C • lam - ∑ i ∈ b.support, a i • σ i
  have hy : ∀ j ∈ b.support, P.toLinearMap y (P.coroot j) = 0 := by
    intro j hj
    have hsum : P.toLinearMap (∑ i ∈ b.support, a i • σ i) (P.coroot j) = a j * c j := by
      rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single j]
      · simp [c]
      · intro i hi hij
        simp [hσ0 i hi j hj (Ne.symm hij)]
      · intro h; exact absurd hj h
    have hprod : a j * c j = C * P.toLinearMap lam (P.coroot j) := by
      simp only [a, C]
      rw [mul_assoc, Finset.prod_erase_mul _ _ hj, mul_comm]
    simp only [y, map_sub, LinearMap.sub_apply, map_zsmul, LinearMap.smul_apply, smul_eq_mul,
      hsum, hprod, sub_self]
  obtain ⟨m, hm, hmy⟩ := hX0 y hy
  refine ⟨m * C.toNat, Nat.mul_pos hm (by omega), ?_⟩
  have heq : (m * C.toNat) • lam =
      m • y + ∑ i ∈ b.support, (m * (a i).toNat) • σ i := by
    have hCn : ((C.toNat : ℕ) : ℤ) = C := Int.toNat_of_nonneg hC.le
    have han : ∀ i ∈ b.support, (((a i).toNat : ℕ) : ℤ) = a i :=
      fun i hi => Int.toNat_of_nonneg (ha i hi)
    have hs : ∑ i ∈ b.support, (m * (a i).toNat) • σ i =
        ∑ i ∈ b.support, ((m : ℤ) * a i) • σ i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [← natCast_zsmul, Nat.cast_mul, han i hi]
    rw [hs, ← natCast_zsmul, ← natCast_zsmul, Nat.cast_mul, hCn]
    simp only [y, smul_sub, Finset.smul_sum, smul_smul]
    abel
  rw [heq]
  exact S.add_mem hmy (S.sum_mem fun i hi => S.nsmul_mem (hσS i hi) _)

end Langlands.RootDatum.DominantMultiple
