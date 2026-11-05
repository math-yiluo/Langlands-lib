import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Bialgebra.Primitive
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Data.Finsupp.Weight
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Minimal relations among primitive elements are additive -/

noncomputable section

open MvPolynomial TensorProduct Coalgebra

namespace Langlands.Algebra.PTorsionHopf

variable {k : Type*} [Field k] {s : ℕ}

/-- The comultiplication of the additive polynomial bialgebra: `Xᵢ ↦ Xᵢ ⊗ 1 + 1 ⊗ Xᵢ`. -/
def addComul : MvPolynomial (Fin s) k →ₐ[k] MvPolynomial (Fin s) k ⊗[k] MvPolynomial (Fin s) k :=
  aeval fun i => X i ⊗ₜ[k] (1 : MvPolynomial (Fin s) k) + (1 : MvPolynomial (Fin s) k) ⊗ₜ[k] X i

theorem addComul_X (i : Fin s) :
    addComul (k := k) (s := s) (X i) = X i ⊗ₜ[k] (1 : MvPolynomial (Fin s) k) + (1 : MvPolynomial (Fin s) k) ⊗ₜ[k] X i := by
  simp [addComul]

/-- The failure of additivity of a polynomial. -/
def addDefect : MvPolynomial (Fin s) k →ₗ[k] MvPolynomial (Fin s) k ⊗[k] MvPolynomial (Fin s) k :=
  (addComul (k := k) (s := s)).toLinearMap - (TensorProduct.mk k (MvPolynomial (Fin s) k) (MvPolynomial (Fin s) k)).flip 1 - TensorProduct.mk k (MvPolynomial (Fin s) k) (MvPolynomial (Fin s) k) 1

theorem addDefect_apply (F : MvPolynomial (Fin s) k) :
    addDefect F = addComul (k := k) (s := s) F - F ⊗ₜ[k] (1 : MvPolynomial (Fin s) k) - (1 : MvPolynomial (Fin s) k) ⊗ₜ[k] F := rfl

theorem addDefect_mul_X (P : MvPolynomial (Fin s) k) (i : Fin s) :
    addDefect (P * X i) = P ⊗ₜ[k] X i + X i ⊗ₜ[k] P +
      addDefect P * (X i ⊗ₜ[k] (1 : MvPolynomial (Fin s) k) + (1 : MvPolynomial (Fin s) k) ⊗ₜ[k] X i) := by
  have e1 : (P * X i) ⊗ₜ[k] (1 : MvPolynomial (Fin s) k) =
      (P ⊗ₜ[k] (1 : MvPolynomial (Fin s) k)) * (X i ⊗ₜ[k] (1 : MvPolynomial (Fin s) k)) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have e2 : (1 : MvPolynomial (Fin s) k) ⊗ₜ[k] (P * X i) =
      ((1 : MvPolynomial (Fin s) k) ⊗ₜ[k] P) * ((1 : MvPolynomial (Fin s) k) ⊗ₜ[k] X i) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have e3 : P ⊗ₜ[k] (X i : MvPolynomial (Fin s) k) =
      (P ⊗ₜ[k] (1 : MvPolynomial (Fin s) k)) * ((1 : MvPolynomial (Fin s) k) ⊗ₜ[k] X i) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have e4 : (X i : MvPolynomial (Fin s) k) ⊗ₜ[k] P =
      ((1 : MvPolynomial (Fin s) k) ⊗ₜ[k] P) * (X i ⊗ₜ[k] (1 : MvPolynomial (Fin s) k)) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [addDefect_apply, addDefect_apply, map_mul, addComul_X, e1, e2, e3, e4]
  ring

/-- Tensors of polynomials of total degree at most `m`. -/
def lowTensor (m : ℕ) : Submodule k (MvPolynomial (Fin s) k ⊗[k] MvPolynomial (Fin s) k) :=
  LinearMap.range (TensorProduct.map (restrictTotalDegree (Fin s) k m).subtype
    (restrictTotalDegree (Fin s) k m).subtype)

theorem tmul_mem_lowTensor {m : ℕ} {a b : MvPolynomial (Fin s) k} (ha : a.totalDegree ≤ m) (hb : b.totalDegree ≤ m) :
    a ⊗ₜ[k] b ∈ lowTensor m :=
  ⟨⟨a, (mem_restrictTotalDegree _ _ _).2 ha⟩ ⊗ₜ ⟨b, (mem_restrictTotalDegree _ _ _).2 hb⟩, rfl⟩

theorem lowTensor_mono {m m' : ℕ} (h : m ≤ m') : lowTensor (k := k) (s := s) m ≤ lowTensor m' := by
  rw [lowTensor, range_map_eq_span_tmul, Submodule.span_le]
  rintro _ ⟨a, b, rfl⟩
  exact tmul_mem_lowTensor (((mem_restrictTotalDegree _ _ _).1 a.2).trans h)
    (((mem_restrictTotalDegree _ _ _).1 b.2).trans h)

theorem mul_mem_lowTensor {m : ℕ} {t : MvPolynomial (Fin s) k ⊗[k] MvPolynomial (Fin s) k} (ht : t ∈ lowTensor m) (i : Fin s) :
    t * (X i ⊗ₜ[k] (1 : MvPolynomial (Fin s) k) + (1 : MvPolynomial (Fin s) k) ⊗ₜ[k] X i) ∈ lowTensor (m + 1) := by
  rw [lowTensor, range_map_eq_span_tmul] at ht
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, b, rfl⟩ := hx
    have ha := (mem_restrictTotalDegree _ _ _).1 a.2
    have hb := (mem_restrictTotalDegree _ _ _).1 b.2
    have hX : (X i : MvPolynomial (Fin s) k).totalDegree ≤ 1 := (totalDegree_X i).le
    rw [mul_add, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, mul_one]
    refine Submodule.add_mem _ (tmul_mem_lowTensor ?_ (hb.trans (Nat.le_succ m)))
      (tmul_mem_lowTensor (ha.trans (Nat.le_succ m)) ?_)
    · exact (totalDegree_mul _ _).trans (by simp only [Submodule.coe_subtype] at *; omega)
    · exact (totalDegree_mul _ _).trans (by simp only [Submodule.coe_subtype] at *; omega)
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

theorem addDefect_X (i : Fin s) : addDefect (k := k) (X i : MvPolynomial (Fin s) k) = 0 := by
  rw [addDefect_apply, addComul_X]
  abel

/-- The additivity defect of a monomial of degree `n + 1` is a tensor of polynomials of degree
at most `n`. -/
theorem addDefect_monomial_mem (n : ℕ) :
    ∀ α : Fin s →₀ ℕ, α.degree = n + 1 → addDefect (monomial α (1 : k)) ∈ lowTensor n := by
  induction n with
  | zero =>
    intro α hα
    obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
      by_contra h
      push Not at h
      have : α = 0 := Finsupp.ext h
      rw [this, map_zero] at hα
      exact absurd hα (by norm_num)
    have hle : α i ≤ α.degree := Finsupp.le_degree i α
    have hαi : α = Finsupp.single i 1 := by
      ext j
      by_cases hj : j = i
      · subst hj
        rw [Finsupp.single_eq_same]
        omega
      · rw [Finsupp.single_eq_of_ne hj]
        by_contra hne
        have h2 : α i + α j ≤ α.degree := by
          rw [Finsupp.degree_apply]
          have hsub : ({i, j} : Finset (Fin s)) ⊆ α.support := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl <;> simpa using ‹_›
          calc α i + α j = ∑ x ∈ ({i, j} : Finset (Fin s)), α x := by
                rw [Finset.sum_pair (Ne.symm hj)]
            _ ≤ ∑ x ∈ α.support, α x := Finset.sum_le_sum_of_subset hsub
        omega
    rw [hαi, ← X, addDefect_X]
    exact Submodule.zero_mem _
  | succ n ih =>
    intro α hα
    obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
      by_contra h
      push Not at h
      have : α = 0 := Finsupp.ext h
      rw [this, map_zero] at hα
      omega
    set α' := α - Finsupp.single i 1 with hα'
    have hle : Finsupp.single i 1 ≤ α := by
      intro j
      by_cases hj : j = i
      · subst hj; rw [Finsupp.single_eq_same]; omega
      · rw [Finsupp.single_eq_of_ne hj]; exact Nat.zero_le _
    have hαeq : α = α' + Finsupp.single i 1 := (tsub_add_cancel_of_le hle).symm
    have hdeg : α'.degree = n + 1 := by
      have := congrArg Finsupp.degree hαeq
      rw [map_add, Finsupp.degree_single] at this
      omega
    rw [hαeq, ← mul_one (1 : k), ← monomial_mul_monomial, ← X, addDefect_mul_X]
    have hdeg' : (monomial α' (1 : k)).totalDegree ≤ n + 1 := by
      rw [totalDegree_monomial _ one_ne_zero]
      exact hdeg.le
    have hX : (X i : MvPolynomial (Fin s) k).totalDegree ≤ n + 1 := by
      rw [totalDegree_X]; omega
    refine Submodule.add_mem _ (Submodule.add_mem _ (tmul_mem_lowTensor hdeg' hX)
      (tmul_mem_lowTensor hX hdeg')) (mul_mem_lowTensor (ih α' hdeg) i)

/-- A polynomial of total degree at most `d + 1` without constant term has additivity defect in
the tensors of polynomials of degree at most `d`. -/
theorem addDefect_mem_lowTensor {d : ℕ} {F : MvPolynomial (Fin s) k} (hF : F.totalDegree ≤ d + 1)
    (h0 : constantCoeff F = 0) : addDefect F ∈ lowTensor d := by
  rw [F.as_sum, map_sum]
  refine Submodule.sum_mem _ fun α hα => ?_
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [mem_support_iff] at hα
    exact hα h0
  have hdeg : α.degree ≤ d + 1 := (le_totalDegree hα).trans hF
  have hpos : α.degree ≠ 0 := fun h => hα0 ((Finsupp.degree_eq_zero_iff α).1 h)
  rw [← mul_one (F.coeff α), ← smul_eq_mul, ← smul_monomial, map_smul]
  refine Submodule.smul_mem _ _ (lowTensor_mono ?_ (addDefect_monomial_mem (α.degree - 1) α
    (by omega)))
  omega

/-- A vanishing additivity defect gives additivity under evaluation in every commutative
algebra. -/
theorem aeval_add_of_addDefect_eq_zero {F : MvPolynomial (Fin s) k} (hF : addDefect F = 0)
    {R : Type*} [CommRing R] [Algebra k R] (u v : Fin s → R) :
    aeval (u + v) F = aeval u F + aeval v F := by
  let L : MvPolynomial (Fin s) k ⊗[k] MvPolynomial (Fin s) k →ₐ[k] R :=
    Algebra.TensorProduct.lift (aeval u) (aeval v) (fun _ _ => Commute.all _ _)
  have hL : L.comp (addComul (k := k) (s := s)) = aeval (u + v) := by
    ext i
    simp [L, addComul_X]
  have h := congrArg L hF
  rw [addDefect_apply, map_sub, map_sub, map_zero, sub_sub, sub_eq_zero] at h
  rw [← hL, AlgHom.comp_apply, h]
  simp [L]

variable {A : Type*} [CommRing A] [Bialgebra k A]

/-- Comultiplication of a polynomial in primitive elements. -/
theorem comul_aeval_primitive {y : Fin s → A} (hy : ∀ i, Bialgebra.IsPrimitiveElem k (y i))
    (F : MvPolynomial (Fin s) k) :
    comul (R := k) (aeval y F) =
      Algebra.TensorProduct.map (aeval y) (aeval y) (addComul (k := k) (s := s) F) := by
  have h : (Bialgebra.comulAlgHom k A).comp (aeval y) =
      (Algebra.TensorProduct.map (aeval y) (aeval y)).comp (addComul (k := k) (s := s)) := by
    ext i
    simp only [AlgHom.comp_apply, aeval_X, Bialgebra.comulAlgHom_apply, addComul_X, map_add,
      Algebra.TensorProduct.map_tmul, map_one, (hy i).comul_eq_tmul_add_tmul]
    rw [add_comm]
  have := AlgHom.congr_fun h F
  simpa only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply] using this

/-- The counit of a polynomial in primitive elements is its constant coefficient. -/
theorem counit_aeval_primitive {y : Fin s → A} (hy : ∀ i, Bialgebra.IsPrimitiveElem k (y i))
    (F : MvPolynomial (Fin s) k) : counit (R := k) (aeval y F) = constantCoeff F := by
  have h : (Bialgebra.counitAlgHom k A).comp (aeval y) = aeval (0 : Fin s → k) := by
    ext i
    simp [(hy i).counit_eq_zero]
  have := AlgHom.congr_fun h F
  rw [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply] at this
  rw [this, ← eval_zero]
  rfl

/-- **Minimal relations among primitive elements are additive.** If `F` is a relation among
primitive elements and no nonzero relation has smaller total degree, then `F` has vanishing
additivity defect. -/
theorem addDefect_eq_zero_of_minimal {y : Fin s → A} (hy : ∀ i, Bialgebra.IsPrimitiveElem k (y i))
    {F : MvPolynomial (Fin s) k} (hF : aeval y F = 0)
    (hmin : ∀ G : MvPolynomial (Fin s) k, aeval y G = 0 → G.totalDegree < F.totalDegree → G = 0) :
    addDefect F = 0 := by
  have h0 : constantCoeff F = 0 := by rw [← counit_aeval_primitive hy, hF, map_zero]
  rcases Nat.eq_zero_or_pos F.totalDegree with hd | hd
  · have hc0 : F.coeff 0 = 0 := h0
    have : F = 0 := by rw [totalDegree_eq_zero_iff_eq_C.1 hd, hc0, map_zero]
    rw [this, map_zero]
  · obtain ⟨t, ht⟩ := addDefect_mem_lowTensor (d := F.totalDegree - 1) (by omega) h0
    let ι := (restrictTotalDegree (Fin s) k (F.totalDegree - 1)).subtype
    have hinj : Function.Injective ((aeval y).toLinearMap ∘ₗ ι) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro G hG
      have hGdeg := (mem_restrictTotalDegree _ _ _).1 G.2
      exact Subtype.ext (hmin G.1 hG (by omega))
    have hinj2 := TensorProduct.map_injective_of_flat_flat _ _ hinj hinj
    have hχ : Algebra.TensorProduct.map (aeval y) (aeval y) (addDefect F) = 0 := by
      rw [addDefect_apply, map_sub, map_sub, ← comul_aeval_primitive hy, hF, map_zero,
        Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, hF, TensorProduct.zero_tmul,
        TensorProduct.tmul_zero, sub_zero, sub_zero]
    have hcomp : ∀ u, Algebra.TensorProduct.map (aeval y) (aeval y) (TensorProduct.map ι ι u) =
        TensorProduct.map ((aeval y).toLinearMap ∘ₗ ι) ((aeval y).toLinearMap ∘ₗ ι) u := by
      intro u
      induction u using TensorProduct.inductionOn with
      | tmul a b => rfl
      | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
    have ht0 : t = 0 := hinj2 (by rw [← hcomp, ht, hχ, map_zero])
    rw [← ht, ht0, map_zero]

end Langlands.Algebra.PTorsionHopf
