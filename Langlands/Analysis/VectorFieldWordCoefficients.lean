import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-! # Coordinate coefficients of words in vector fields -/

noncomputable section

open scoped ContDiff Topology
open Set Filter

set_option autoImplicit false

namespace Langlands.Analysis

variable {d n : ℕ}

local notation "F" => EuclideanSpace ℝ (Fin d)
local notation "e" => EuclideanSpace.basisFun (Fin d) ℝ

/-- The coefficients of the composite `∂_{V i₁} ∘ ⋯ ∘ ∂_{V iₖ}` of directional derivatives along
the vector fields `V i` in ordered standard coordinate derivatives. The value
`vectorFieldWordCoeff V w k W x` is the coefficient of `D^k u x (e (W 0), …, e (W (k-1)))`. -/
def vectorFieldWordCoeff (V : Fin n → F → F) :
    List (Fin n) → (k : ℕ) → (Fin k → Fin d) → F → ℂ
  | [], 0, _ => fun _ => 1
  | [], _ + 1, _ => fun _ => 0
  | i :: w, 0, W => fun x => fderiv ℝ (vectorFieldWordCoeff V w 0 W) x (V i x)
  | i :: w, k + 1, W => fun x =>
      fderiv ℝ (vectorFieldWordCoeff V w (k + 1) W) x (V i x) +
        ((V i x) (W 0) : ℂ) * vectorFieldWordCoeff V w k (Fin.tail W) x

/-- The coefficients of orders above the word length vanish. -/
theorem vectorFieldWordCoeff_eq_zero (V : Fin n → F → F) :
    ∀ (w : List (Fin n)) (k : ℕ) (W : Fin k → Fin d), w.length < k →
      vectorFieldWordCoeff V w k W = 0
  | [], 0, _, h => absurd h (by simp)
  | [], _ + 1, _, _ => rfl
  | _ :: _, 0, _, h => absurd h (by simp)
  | i :: w, k + 1, W, h => by
      have h' : w.length < k := by simpa using h
      have h1 := vectorFieldWordCoeff_eq_zero V w (k + 1) W (by omega)
      have h2 := vectorFieldWordCoeff_eq_zero V w k (Fin.tail W) h'
      funext x
      simp only [vectorFieldWordCoeff, h1, h2, fderiv_zero, Pi.zero_apply, mul_zero, add_zero,
        zero_apply]

/-- The coefficients are smooth where the vector fields are smooth. -/
theorem contDiffOn_vectorFieldWordCoeff {V : Fin n → F → F} {S : Set F} (hS : IsOpen S)
    (hV : ∀ i, ContDiffOn ℝ ∞ (V i) S) :
    ∀ (w : List (Fin n)) (k : ℕ) (W : Fin k → Fin d),
      ContDiffOn ℝ ∞ (vectorFieldWordCoeff V w k W) S
  | [], 0, _ => contDiffOn_const
  | [], _ + 1, _ => contDiffOn_const
  | i :: w, 0, W => by
      have h := contDiffOn_vectorFieldWordCoeff hS hV w 0 W
      exact (h.fderiv_of_isOpen hS (by simp)).clm_apply (hV i)
  | i :: w, k + 1, W => by
      have h1 := contDiffOn_vectorFieldWordCoeff hS hV w (k + 1) W
      have h2 := contDiffOn_vectorFieldWordCoeff hS hV w k (Fin.tail W)
      have h3 : ContDiffOn ℝ ∞ (fun x => (((V i x) (W 0) : ℝ) : ℂ)) S :=
        Complex.ofRealCLM.contDiff.comp_contDiffOn
          ((EuclideanSpace.proj (W 0) : F →L[ℝ] ℝ).contDiff.comp_contDiffOn (hV i))
      exact ((h1.fderiv_of_isOpen hS (by simp)).clm_apply (hV i)).add (h3.mul h2)

/-- Contracting the first slot of the next derivative with the coordinates of `v` gives the
directional derivative along `v`. -/
theorem sum_coord_mul_iteratedFDeriv_cons (k : ℕ) (W : Fin k → Fin d) {u : F → ℂ} {x : F}
    (hu : ContDiffAt ℝ ∞ u x) (v : F) :
    ∑ j : Fin d, ((v j : ℝ) : ℂ) *
        iteratedFDeriv ℝ (k + 1) u x (fun q => e ((Fin.cons j W : Fin (k + 1) → Fin d) q)) =
      fderiv ℝ (fun y => iteratedFDeriv ℝ k u y (fun q => e (W q))) x v := by
  have hd := hu.differentiableAt_iteratedFDeriv (m := k)
    (by exact_mod_cast ENat.natCast_lt_top k)
  simp_rw [hd.iteratedFDeriv_succ_apply_left']
  have htail (j : Fin d) :
      Fin.tail (fun q : Fin (k + 1) => e ((Fin.cons j W : Fin (k + 1) → Fin d) q)) =
        fun q => e (W q) := by
    funext q
    simp [Fin.tail]
  simp only [htail, Fin.cons_zero]
  set L := fderiv ℝ (fun y => iteratedFDeriv ℝ k u y (fun q => e (W q))) x
  have h := congrArg L ((EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v)
  simpa only [map_sum, map_smul, EuclideanSpace.basisFun_repr, Complex.real_smul] using h

/-- Splitting a sum over `(k + 1)`-tuples into the first entry and the remaining `k`-tuple. -/
theorem sum_fun_fin_succ {β : Type*} [AddCommMonoid β] (k : ℕ)
    (f : (Fin (k + 1) → Fin d) → β) :
    ∑ W : Fin (k + 1) → Fin d, f W =
      ∑ j : Fin d, ∑ W : Fin k → Fin d, f (Fin.cons j W : Fin (k + 1) → Fin d) := by
  rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Fin d)).sum_comp, Fintype.sum_prod_type]
  rfl

private theorem prepend_sum (k : ℕ) (a : (Fin k → Fin d) → ℂ) {u : F → ℂ} {x : F}
    (hu : ContDiffAt ℝ ∞ u x) (v : F) :
    ∑ W : Fin (k + 1) → Fin d,
        ((v (W 0) : ℝ) : ℂ) * a (Fin.tail W) * iteratedFDeriv ℝ (k + 1) u x (fun q => e (W q)) =
      ∑ W : Fin k → Fin d,
        a W * fderiv ℝ (fun y => iteratedFDeriv ℝ k u y (fun q => e (W q))) x v := by
  rw [sum_fun_fin_succ]
  simp only [Fin.cons_zero, Fin.tail_cons]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [← sum_coord_mul_iteratedFDeriv_cons k W hu v, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem fderiv_wordArray (a : (k : ℕ) → (Fin k → Fin d) → F → ℂ) (N : ℕ) {u : F → ℂ}
    {x : F} (ha : ∀ k W, DifferentiableAt ℝ (a k W) x) (hu : ContDiffAt ℝ ∞ u x) (v : F) :
    fderiv ℝ (fun y => ∑ k ∈ Finset.range (N + 1), ∑ W : Fin k → Fin d,
        a k W y * iteratedFDeriv ℝ k u y (fun q => e (W q))) x v =
      ∑ k ∈ Finset.range (N + 1), ∑ W : Fin k → Fin d,
        (fderiv ℝ (a k W) x v * iteratedFDeriv ℝ k u x (fun q => e (W q)) +
          a k W x * fderiv ℝ (fun y => iteratedFDeriv ℝ k u y (fun q => e (W q))) x v) := by
  have hd (k : ℕ) (W : Fin k → Fin d) :
      DifferentiableAt ℝ (fun y => iteratedFDeriv ℝ k u y (fun q => e (W q))) x :=
    (hu.differentiableAt_iteratedFDeriv (m := k)
      (by exact_mod_cast ENat.natCast_lt_top k)).continuousMultilinear_apply_const _
  rw [fderiv_fun_sum (u := Finset.range (N + 1))
    (A := fun k y => ∑ W : Fin k → Fin d, a k W y * iteratedFDeriv ℝ k u y (fun q => e (W q)))
    (fun k _ => DifferentiableAt.fun_sum (fun W _ => (ha k W).mul (hd k W)))]
  simp only [sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [fderiv_fun_sum (u := Finset.univ)
    (A := fun W y => a k W y * iteratedFDeriv ℝ k u y (fun q => e (W q)))
    (fun W _ => (ha k W).mul (hd k W))]
  simp only [sum_apply]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [fderiv_fun_mul (ha k W) (hd k W)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- **Coordinate expansion of a word in vector fields.** Let `G w` be functions indexed by words,
with `G [] = u` and `G (i :: w) = ∂_{V i} (G w)` on an open set `S` where `u` and the vector
fields are smooth. Then on `S`, `G w` is the sum of the ordered coordinate derivatives of `u` of
order at most `N` (any `N ≥ w.length`), weighted by `vectorFieldWordCoeff V w`. -/
theorem vectorFieldWord_expansion {V : Fin n → F → F} {S : Set F} (hS : IsOpen S)
    (hV : ∀ i, ContDiffOn ℝ ∞ (V i) S) {u : F → ℂ} (hu : ContDiffOn ℝ ∞ u S)
    (G : List (Fin n) → F → ℂ) (hG0 : ∀ x ∈ S, G [] x = u x)
    (hGs : ∀ i w, ∀ x ∈ S, G (i :: w) x = fderiv ℝ (G w) x (V i x)) :
    ∀ (w : List (Fin n)) (N : ℕ), w.length ≤ N → ∀ x ∈ S,
      G w x = ∑ k ∈ Finset.range (N + 1), ∑ W : Fin k → Fin d,
        vectorFieldWordCoeff V w k W x * iteratedFDeriv ℝ k u x (fun q => e (W q))
  | [], N, _, x, hx => by
      rw [hG0 x hx, Finset.sum_range_succ']
      simp [vectorFieldWordCoeff]
  | i :: w, N, hN, x, hx => by
      have hN' : w.length + 1 ≤ N := by simpa using hN
      obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
      have hIH := vectorFieldWord_expansion hS hV hu G hG0 hGs w (M + 1) (by omega)
      have hcd (k : ℕ) (W : Fin k → Fin d) : DifferentiableAt ℝ (vectorFieldWordCoeff V w k W) x :=
        ((contDiffOn_vectorFieldWordCoeff hS hV w k W).contDiffAt
          (hS.mem_nhds hx)).differentiableAt (by simp)
      have hux : ContDiffAt ℝ ∞ u x := hu.contDiffAt (hS.mem_nhds hx)
      have hEq : G w =ᶠ[𝓝 x] fun y => ∑ k ∈ Finset.range (M + 1 + 1), ∑ W : Fin k → Fin d,
          vectorFieldWordCoeff V w k W y * iteratedFDeriv ℝ k u y (fun q => e (W q)) := by
        filter_upwards [hS.mem_nhds hx] with y hy using hIH y hy
      rw [hGs i w x hx, hEq.fderiv_eq, fderiv_wordArray _ _ hcd hux]
      simp only [Finset.sum_add_distrib]
      have key : ∀ A B T : ℕ → ℂ, T 0 = A 0 → (∀ k < M + 1, T (k + 1) = A (k + 1) + B k) →
          B (M + 1) = 0 →
          ∑ k ∈ Finset.range (M + 1 + 1), A k + ∑ k ∈ Finset.range (M + 1 + 1), B k =
            ∑ k ∈ Finset.range (M + 1 + 1), T k := by
        intro A B T h0 hT hB
        rw [Finset.sum_range_succ' T, h0, Finset.sum_range_succ' A, Finset.sum_range_succ B, hB,
          add_zero, Finset.sum_congr rfl (fun k hk => hT k (Finset.mem_range.1 hk)),
          Finset.sum_add_distrib]
        ring
      refine key _ _ _ ?_ ?_ ?_
      · simp only [vectorFieldWordCoeff]
      · intro k _
        beta_reduce
        rw [← prepend_sum k (fun W => vectorFieldWordCoeff V w k W x) hux (V i x),
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun W _ => ?_
        simp only [vectorFieldWordCoeff]
        ring
      · beta_reduce
        refine Finset.sum_eq_zero fun W _ => ?_
        rw [vectorFieldWordCoeff_eq_zero V w (M + 1) W (by omega)]
        simp

/-- **Top-order coefficients.** Pairing the top-order coefficients of a word with the products of
the values of a real covector on the basis gives the product of the values of the covector on
the vector fields. -/
theorem vectorFieldWordCoeff_symbol (V : Fin n → F → F) (x : F) (ξ : F →L[ℝ] ℝ) :
    ∀ w : List (Fin n), ∑ W : Fin w.length → Fin d,
      vectorFieldWordCoeff V w w.length W x * ∏ j : Fin w.length, ((ξ (e (W j)) : ℝ) : ℂ) =
        (w.map fun a => ((ξ (V a x) : ℝ) : ℂ)).prod
  | [] => by simp [vectorFieldWordCoeff]
  | i :: w => by
      have IH := vectorFieldWordCoeff_symbol V x ξ w
      have hz (W : Fin (w.length + 1) → Fin d) :
          vectorFieldWordCoeff V w (w.length + 1) W = 0 :=
        vectorFieldWordCoeff_eq_zero V w _ W (Nat.lt_succ_self _)
      have hξ : ((ξ (V i x) : ℝ) : ℂ) =
          ∑ a : Fin d, (((V i x) a : ℝ) : ℂ) * ((ξ (e a) : ℝ) : ℂ) := by
        have h := congrArg ξ ((EuclideanSpace.basisFun (Fin d) ℝ).sum_repr (V i x))
        rw [map_sum] at h
        simp only [map_smul, smul_eq_mul, EuclideanSpace.basisFun_repr] at h
        rw [← h]
        push_cast
        rfl
      change ∑ W : Fin (w.length + 1) → Fin d, vectorFieldWordCoeff V (i :: w) (w.length + 1) W x *
          ∏ j : Fin (w.length + 1), ((ξ (e (W j)) : ℝ) : ℂ) = _
      rw [sum_fun_fin_succ]
      simp only [vectorFieldWordCoeff, hz, fderiv_zero, Pi.zero_apply, zero_apply,
        zero_add, Fin.cons_zero, Fin.tail_cons, Fin.prod_univ_succ, Fin.cons_succ]
      rw [List.map_cons, List.prod_cons, ← IH, hξ, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun W _ => ?_
      ring

end Langlands.Analysis
