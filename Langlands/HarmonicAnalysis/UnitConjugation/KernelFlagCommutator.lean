import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Langlands.Algebra.RegularTrace

/-!
# The kernel flag nilradical in the range of the commutator map

For a finite-dimensional semisimple algebra `A` over a field `F` of characteristic zero, the
trace form `(x, y) ↦ tr(z ↦ x y z)` is nondegenerate (`eq_zero_of_forall_regularTrace_mul_eq_zero`),
so the range of `y ↦ x y - y x` is the trace-orthogonal of the centralizer of `x`
(`exists_commutator_eq_of_regularTrace`). If orthogonal idempotents `e 0, …, e (m - 1)` with sum
`1` split the flag of left ideals `J_k = {v | v x ^ k = 0}` (`IsKernelFlagSplitting`), every `w`
with `e i w e j = 0` for `i ≤ j` is such a commutator
(`IsKernelFlagSplitting.exists_commutator_eq`).
A subring containing idempotent generators of all left ideals contains such a splitting
(`exists_isKernelFlagSplitting`).
-/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open Module Finset

open Langlands.Algebra (regularTrace regularTrace_mul_comm regularTraceForm
  regularTraceForm_apply)

variable {F : Type*} [Field F] {A : Type*} [Ring A] [Algebra F A]

/-- In a finite-dimensional semisimple algebra over a field of characteristic zero, an element `y`
with `tr(L_{y z}) = 0` for every `z` is zero. -/
theorem eq_zero_of_forall_regularTrace_mul_eq_zero [CharZero F] [FiniteDimensional F A]
    [IsSemisimpleRing A] {y : A} (hy : ∀ z, regularTrace F A (y * z) = 0) : y = 0 := by
  let I : Submodule A A :=
    { carrier := {y | ∀ z, regularTrace F A (y * z) = 0}
      add_mem' := fun {a b} ha hb z => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [add_mul, map_add, ha z, hb z, add_zero]
      zero_mem' := fun z => by simp
      smul_mem' := fun a y hy z => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul] at hy ⊢
        rw [mul_assoc, regularTrace_mul_comm, mul_assoc]
        exact hy _ }
  have hmemI : ∀ {y : A}, y ∈ I ↔ ∀ z, regularTrace F A (y * z) = 0 := Iff.rfl
  obtain ⟨C, hC⟩ := exists_isCompl I
  have h1 : (1 : A) ∈ I ⊔ C := by rw [hC.sup_eq_top]; trivial
  obtain ⟨e, he, f, hf, hef⟩ := Submodule.mem_sup.mp h1
  have hright : ∀ y ∈ I, y = y * e := by
    intro y hyI
    have hyf : y * f ∈ C := C.smul_mem y hf
    have hye : y * e ∈ I := I.smul_mem y he
    have hyf' : y * f ∈ I := by
      have hsum : y * e + y * f = y := by rw [← mul_add, hef, mul_one]
      rw [eq_sub_of_add_eq' hsum]
      exact I.sub_mem hyI hye
    have h0 : y * f = 0 := (Submodule.disjoint_def.mp hC.disjoint) _ hyf' hyf
    calc y = y * (e + f) := by rw [hef, mul_one]
      _ = y * e := by rw [mul_add, h0, add_zero]
  have hidem : IsIdempotentElem (Algebra.lmul F A e) := by
    show Algebra.lmul F A e * Algebra.lmul F A e = Algebra.lmul F A e
    rw [← map_mul, ← hright e he]
  have htr : LinearMap.trace F A (Algebra.lmul F A e) = 0 := by
    have := (hmemI.mp he) 1
    rwa [mul_one] at this
  have hlmul : Algebra.lmul F A e = 0 :=
    LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hidem htr
  have he0 : e = 0 := by
    have := congrArg (fun φ : Module.End F A => φ 1) hlmul
    simpa using this
  rw [hright y hy, he0, mul_zero]

/-- Over a field of characteristic zero the trace form of a finite-dimensional semisimple algebra
is nondegenerate. -/
theorem regularTraceForm_nondegenerate_of_isSemisimpleRing [CharZero F] [FiniteDimensional F A]
    [IsSemisimpleRing A] :
    (regularTraceForm F A).Nondegenerate := by
  refine ⟨fun y hy => eq_zero_of_forall_regularTrace_mul_eq_zero fun z => hy z,
    fun y hy => eq_zero_of_forall_regularTrace_mul_eq_zero (F := F) fun z => ?_⟩
  rw [regularTrace_mul_comm]
  exact hy z

/-- In a finite-dimensional semisimple algebra over a field of characteristic zero, an element
that is trace-orthogonal to the centralizer of `x` is a commutator `x y - y x`. -/
theorem exists_commutator_eq_of_regularTrace [CharZero F] [FiniteDimensional F A]
    [IsSemisimpleRing A] (x w : A)
    (hw : ∀ z, x * z = z * x → regularTrace F A (w * z) = 0) :
    ∃ y, x * y - y * x = w := by
  let D : A →ₗ[F] A := LinearMap.mulLeft F x - LinearMap.mulRight F x
  have hD : ∀ y, D y = x * y - y * x := fun y => rfl
  let B := regularTraceForm F A
  have hle : LinearMap.range D ≤ B.orthogonal (LinearMap.ker D) := by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro z hz
    have hz' : x * z = z * x := by
      have : D z = 0 := hz
      rw [hD, sub_eq_zero] at this
      exact this
    change regularTrace F A (z * (x * y - y * x)) = 0
    rw [mul_sub, map_sub, ← mul_assoc, ← hz', mul_assoc, regularTrace_mul_comm F A x (z * y),
      ← mul_assoc, sub_self]
  have hfin : Module.finrank F (LinearMap.range D) =
      Module.finrank F (B.orthogonal (LinearMap.ker D)) := by
    rw [LinearMap.BilinForm.finrank_orthogonal regularTraceForm_nondegenerate_of_isSemisimpleRing]
    have := LinearMap.finrank_range_add_finrank_ker D
    omega
  have heq : LinearMap.range D = B.orthogonal (LinearMap.ker D) :=
    Submodule.eq_of_le_of_finrank_eq hle hfin
  have hwmem : w ∈ B.orthogonal (LinearMap.ker D) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro z hz
    have hz' : x * z = z * x := by
      have : D z = 0 := hz
      rw [hD, sub_eq_zero] at this
      exact this
    change regularTrace F A (z * w) = 0
    rw [regularTrace_mul_comm]
    exact hw z hz'
  rw [← heq] at hwmem
  obtain ⟨y, hy⟩ := hwmem
  exact ⟨y, hy⟩


section Flag

variable {e : ℕ → A}

theorem mul_sum_range_of_lt (he : ∀ i, e i * e i = e i)
    (horth : ∀ i j, i ≠ j → e i * e j = 0) {i k : ℕ} (h : i < k) :
    e i * ∑ l ∈ range k, e l = e i := by
  rw [Finset.mul_sum, Finset.sum_eq_single i (fun l _ hl => horth i l (Ne.symm hl))
    (fun hi => absurd (Finset.mem_range.mpr h) hi), he]

theorem mul_sum_range_of_le (horth : ∀ i j, i ≠ j → e i * e j = 0) {i k : ℕ} (h : k ≤ i) :
    e i * ∑ l ∈ range k, e l = 0 := by
  rw [Finset.mul_sum]
  exact Finset.sum_eq_zero fun l hl => horth i l (by have := Finset.mem_range.mp hl; omega)

theorem sum_range_mul_of_lt (he : ∀ i, e i * e i = e i)
    (horth : ∀ i j, i ≠ j → e i * e j = 0) {i k : ℕ} (h : i < k) :
    (∑ l ∈ range k, e l) * e i = e i := by
  rw [Finset.sum_mul, Finset.sum_eq_single i (fun l _ hl => horth l i hl)
    (fun hi => absurd (Finset.mem_range.mpr h) hi), he]

theorem sum_range_mul_of_le (horth : ∀ i j, i ≠ j → e i * e j = 0) {i k : ℕ} (h : k ≤ i) :
    (∑ l ∈ range k, e l) * e i = 0 := by
  rw [Finset.sum_mul]
  exact Finset.sum_eq_zero fun l hl => horth l i (by have := Finset.mem_range.mp hl; omega)

variable (x : A) (m : ℕ)

/-- The hypotheses on a splitting of the kernel flag `J_k = {v | v x ^ k = 0}` of `x` by
orthogonal idempotents `e 0, …, e (m - 1)` with sum `1`: `J_k = A (e 0 + ⋯ + e (k - 1))`. -/
structure IsKernelFlagSplitting (e : ℕ → A) : Prop where
  idem : ∀ i, e i * e i = e i
  orth : ∀ i j, i ≠ j → e i * e j = 0
  sum_eq_one : ∑ i ∈ range m, e i = 1
  flag : ∀ (k : ℕ) (v : A), v * x ^ k = 0 ↔ v * ∑ i ∈ range k, e i = v

variable {x m}

theorem IsKernelFlagSplitting.mul_pow_succ_eq_zero (h : IsKernelFlagSplitting x m e) (i : ℕ) :
    e i * x ^ (i + 1) = 0 := by
  rw [h.flag, mul_sum_range_of_lt h.idem h.orth (Nat.lt_succ_self i)]

/-- Elements commuting with `x` preserve the flag: `e j z e i = 0` for `j < i`. -/
theorem IsKernelFlagSplitting.mul_mul_eq_zero_of_commute (h : IsKernelFlagSplitting x m e)
    {z : A} (hz : x * z = z * x) {i j : ℕ} (hji : j < i) : e j * z * e i = 0 := by
  have hc : Commute z (x ^ (j + 1)) := (Commute.pow_right (Commute.symm hz) (j + 1))
  have h0 : e j * z * x ^ (j + 1) = 0 := by
    rw [mul_assoc, hc.eq, ← mul_assoc, h.mul_pow_succ_eq_zero, zero_mul]
  have h1 := (h.flag (j + 1) (e j * z)).mp h0
  rw [← h1, mul_assoc, sum_range_mul_of_le h.orth (by omega), mul_zero]

/-- `x` lies in the nilradical of the flag: `e i x e j = 0` for `i ≤ j`. -/
theorem IsKernelFlagSplitting.mul_mul_eq_zero_self (h : IsKernelFlagSplitting x m e)
    {i j : ℕ} (hij : i ≤ j) : e i * x * e j = 0 := by
  have h0 : e i * x * x ^ i = 0 := by
    rw [mul_assoc, ← pow_succ', h.mul_pow_succ_eq_zero]
  have h1 := (h.flag i (e i * x)).mp h0
  rw [← h1, mul_assoc, sum_range_mul_of_le h.orth hij, mul_zero]

theorem IsKernelFlagSplitting.regularTrace_eq_sum (h : IsKernelFlagSplitting x m e) (W : A) :
    regularTrace F A W = ∑ i ∈ range m, regularTrace F A (e i * W * e i) := by
  conv_lhs => rw [← one_mul W, ← h.sum_eq_one, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  calc regularTrace F A (e i * W) = regularTrace F A (e i * e i * W) := by rw [h.idem i]
    _ = regularTrace F A (e i * W * e i) := by rw [mul_assoc, regularTrace_mul_comm]

/-- **The range of `y ↦ x y - y x` contains the nilradical of the kernel flag.**
If `e` splits the kernel flag of `x` in a finite-dimensional semisimple algebra over a field
of characteristic zero, every `w` with `e i w e j = 0` for `i ≤ j` is a commutator `x y - y x`. -/
theorem IsKernelFlagSplitting.exists_commutator_eq [CharZero F] [FiniteDimensional F A]
    [IsSemisimpleRing A] (h : IsKernelFlagSplitting x m e) {w : A}
    (hw : ∀ i j, i ≤ j → e i * w * e j = 0) : ∃ y, x * y - y * x = w := by
  refine exists_commutator_eq_of_regularTrace (F := F) x w fun z hz => ?_
  rw [h.regularTrace_eq_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  have : e i * (w * z) * e i = 0 := by
    calc e i * (w * z) * e i = e i * w * (∑ j ∈ range m, e j) * z * e i := by
          rw [h.sum_eq_one, mul_one, mul_assoc (e i) w z]
      _ = ∑ j ∈ range m, e i * w * e j * (z * e i) := by
          rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [mul_assoc]
      _ = 0 := by
          refine Finset.sum_eq_zero fun j _ => ?_
          rcases le_or_gt i j with hij | hji
          · rw [hw i j hij, zero_mul]
          · rw [mul_assoc, ← mul_assoc (e j), h.mul_mul_eq_zero_of_commute hz hji, mul_zero]
  rw [this, map_zero]

section Splitting

variable {B : Type*} [Ring B]

theorem mem_span_singleton_iff_mul_eq {f v : B} (hf : IsIdempotentElem f) :
    v ∈ Submodule.span B {f} ↔ v * f = v := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    rw [smul_eq_mul, mul_assoc, hf.eq]
  · intro h
    exact ⟨v, h⟩

/-- The left ideal `{v | v x ^ k = 0}`. -/
def leftAnnihilatorPow (x : B) (k : ℕ) : Submodule B B where
  carrier := {v | v * x ^ k = 0}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [add_mul, ha, hb, add_zero]
  zero_mem' := by simp
  smul_mem' := fun a v hv => by
    simp only [Set.mem_ofPred_eq, smul_eq_mul] at hv ⊢
    rw [mul_assoc, hv, mul_zero]

theorem mem_leftAnnihilatorPow {x v : B} {k : ℕ} :
    v ∈ leftAnnihilatorPow x k ↔ v * x ^ k = 0 := Iff.rfl

/-- **Splitting the kernel flag inside a subring.** If every left ideal of `B` is generated by an
idempotent of the subring `R`, the kernel flag of an element `x` with `x ^ m = 0` is split by
orthogonal idempotents of `R`. -/
theorem exists_isKernelFlagSplitting (R : Subring B)
    (hR : ∀ J : Submodule B B, ∃ e ∈ R, IsIdempotentElem e ∧ J = Submodule.span B {e})
    {x : B} {m : ℕ} (hx : x ^ m = 0) :
    ∃ e : ℕ → B, (∀ i, e i ∈ R) ∧ IsKernelFlagSplitting x m e := by
  choose f hfR hfi hfJ using fun k => hR (leftAnnihilatorPow x k)
  have hfmem : ∀ k v, v * x ^ k = 0 ↔ v * f k = v := fun k v => by
    rw [← mem_leftAnnihilatorPow, hfJ k, mem_span_singleton_iff_mul_eq (hfi k)]
  obtain ⟨p, hp0, hps⟩ : ∃ p : ℕ → B,
      p 0 = 0 ∧ ∀ k, p (k + 1) = f (k + 1) + p k - f (k + 1) * p k :=
    ⟨fun k => Nat.rec 0 (fun k q => f (k + 1) + q - f (k + 1) * q) k, rfl, fun k => rfl⟩
  -- the properties of `p k`, by induction
  have key : ∀ k, p k ∈ R ∧ IsIdempotentElem (p k) ∧ (∀ v, v * x ^ k = 0 ↔ v * p k = v) := by
    intro k
    induction k with
    | zero =>
      refine ⟨by rw [hp0]; exact R.zero_mem, by rw [hp0]; exact IsIdempotentElem.zero, ?_⟩
      intro v
      simp [hp0, eq_comm]
    | succ k ih =>
      obtain ⟨hR', hidem, hflag⟩ := ih
      set q := p k
      set g := f (k + 1)
      have hg : g * g = g := hfi (k + 1)
      have hq : q * q = q := hidem
      have hqg : q * g = q := by
        have h1 : q * x ^ k = 0 := (hflag q).mpr hq
        have h2 : q * x ^ (k + 1) = 0 := by rw [pow_succ, ← mul_assoc, h1, zero_mul]
        exact (hfmem (k + 1) q).mp h2
      have hgqg : g * q * g = g * q := by rw [mul_assoc, hqg]
      rw [hps k]
      refine ⟨?_, ?_, ?_⟩
      · exact R.sub_mem (R.add_mem (hfR _) hR') (R.mul_mem (hfR _) hR')
      · show (g + q - g * q) * (g + q - g * q) = g + q - g * q
        simp only [sub_mul, add_mul, mul_sub, mul_add]
        simp only [← mul_assoc, hg, hq, hqg, hgqg]
        abel
      · intro v
        rw [hfmem (k + 1) v]
        constructor
        · intro hv
          rw [mul_sub, mul_add, hv, ← mul_assoc, hv]
          abel
        · intro hv
          have hpg : (g + q - g * q) * g = g + q - g * q := by
            simp only [sub_mul, add_mul, hg, hqg, hgqg]
          rw [← hv, mul_assoc, hpg]
  have hpR : ∀ k, p k ∈ R := fun k => (key k).1
  have hpi : ∀ k, p k * p k = p k := fun k => (key k).2.1
  have hpf : ∀ k v, v * x ^ k = 0 ↔ v * p k = v := fun k => (key k).2.2
  -- compatibility of the chain
  have hle : ∀ k l, k ≤ l → p k * p l = p k ∧ p l * p k = p k := by
    intro k l hkl
    induction l, hkl using Nat.le_induction with
    | base => exact ⟨hpi k, hpi k⟩
    | succ l hkl ih =>
      have hql : p l * f (l + 1) = p l := by
        have h1 : p l * x ^ l = 0 := (hpf l (p l)).mpr (hpi l)
        have h2 : p l * x ^ (l + 1) = 0 := by rw [pow_succ, ← mul_assoc, h1, zero_mul]
        exact (hfmem (l + 1) (p l)).mp h2
      have hstep1 : p l * p (l + 1) = p l := by
        rw [hps l, mul_sub, mul_add, hql, hpi l, ← mul_assoc, hql, hpi l]
        abel
      have hstep2 : p (l + 1) * p l = p l := by
        rw [hps l, sub_mul, add_mul, mul_assoc, hpi l]
        abel
      constructor
      · rw [← ih.1, mul_assoc, hstep1]
      · rw [← ih.2, ← mul_assoc, hstep2]
  let e : ℕ → B := fun i => p (i + 1) - p i
  have hsum : ∀ k, ∑ i ∈ range k, e i = p k := fun k => by
    rw [Finset.sum_range_sub (fun i => p i) k, hp0, sub_zero]
  have hpm : p m = 1 := by
    have h := (hpf m 1).mp (by rw [hx, mul_zero])
    rwa [one_mul] at h
  refine ⟨e, fun i => R.sub_mem (hpR (i + 1)) (hpR i), ?_, ?_, ?_, ?_⟩
  · intro i
    have h1 := hle i (i + 1) (Nat.le_succ i)
    show (p (i + 1) - p i) * (p (i + 1) - p i) = p (i + 1) - p i
    rw [sub_mul, mul_sub, mul_sub, hpi, hpi, h1.1, h1.2]
    abel
  · intro i j hij
    show (p (i + 1) - p i) * (p (j + 1) - p j) = 0
    rcases lt_or_gt_of_ne hij with h | h
    · have a1 := hle (i + 1) (j + 1) (by omega)
      have a2 := hle (i + 1) j (by omega)
      have a3 := hle i (j + 1) (by omega)
      have a4 := hle i j (by omega)
      rw [sub_mul, mul_sub, mul_sub, a1.1, a2.1, a3.1, a4.1]
      abel
    · have a1 := hle (j + 1) (i + 1) (by omega)
      have a2 := hle j (i + 1) (by omega)
      have a3 := hle (j + 1) i (by omega)
      have a4 := hle j i (by omega)
      rw [sub_mul, mul_sub, mul_sub, a1.2, a2.2, a3.2, a4.2]
      abel
  · rw [hsum, hpm]
  · intro k v
    rw [hsum, hpf]

end Splitting

end Flag

end Langlands.HarmonicAnalysis.UnitConjugation
