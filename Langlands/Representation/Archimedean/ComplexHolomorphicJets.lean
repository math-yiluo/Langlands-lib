import Langlands.Representation.Archimedean.ComplexHolomorphicFormal
import Langlands.Representation.Archimedean.FormalRealPolynomials
import Langlands.Representation.Archimedean.WeightedWirtinger
import Langlands.Representation.Archimedean.ComplexLinkedSmallGrowthAdjacent

/-!
# Holomorphic jets of principal-series functions

Fix exponents `σ : Fin n → ℂ`. With the Gram weights `T_m = gramWeight m` of the lower rows of
`nbMat v`, `ω = ∏_m T_m^{σ_m}` and `D = ∏_m T_m`, a function `F` *has jet* `Q` (a polynomial in
`v`, in `Pol n`) if for some `N` and some formal real polynomial `P` in `(v, v̄)`,
`F(nbUnit v) D(v)^N = ω(v) P(v, v̄)` and `Q` is `P` with `v̄ = 0` (`HasJet`).

* `gramF m`: the Gram determinants as formal real polynomials; `evalC_gramF`, and
  `holPart_gramF`: with `v̄ = 0` they become `1`.
* `HasJet.unique`: the jet is unique (`evalC_injective`); `HasJet.add`, `HasJet.smul`,
  `hasJet_zero`, `HasJet.sum`: it is linear.
-/

noncomputable section

open scoped Matrix ComplexConjugate

set_option autoImplicit false

namespace Langlands.Archimedean.HolomorphicJets

open MvPolynomial Langlands.GeneralLinear Langlands.Archimedean.NoncompactPicture
open Langlands.Archimedean.MomentSymbols Langlands.Archimedean.RealPolynomialFunctions
open Langlands.Archimedean.AdjacentGrowth Langlands.Archimedean.LevelFunctions
open Langlands.Archimedean.ComplexDuality

variable {n : ℕ}

/-- Formal real polynomials in the coordinates of the lower unipotent group. -/
abbrev R2 (n : ℕ) := MvPolynomial (Lw n × Bool) ℂ

/-- The antiholomorphic copy of the polynomials in `v`. -/
def antiIncl : Hol n →ₐ[ℂ] R2 n := rename fun k => (k, true)

/-- `nbMat v` as a formal matrix. -/
def nbHol : Matrix (Fin n) (Fin n) (R2 n) := (nbH (n := n)).map holIncl

/-- Its formal complex conjugate. -/
def nbAnti : Matrix (Fin n) (Fin n) (R2 n) := (nbH (n := n)).map antiIncl

/-- The Gram determinant of the rows `m, …, n-1`, formally. -/
def gramF (m : Fin n) : R2 n :=
  (nbHol.submatrix (Subtype.val : Tail n m → Fin n) id *
    (nbAnti.submatrix (Subtype.val : Tail n m → Fin n) id)ᵀ).det

theorem nbH_apply (a b : Fin n) :
    nbH a b = (if a = b then 1 else 0) + if h : b < a then (X ⟨(a, b), h⟩ : Hol n) else 0 := by
  simp [nbH, lowMatG, Matrix.one_apply]

theorem nbHol_map_evalC (v : Lw n → ℂ) :
    (nbHol (n := n)).map (fun P => evalC P v) = nbMat v := by
  ext a b
  simp only [Matrix.map_apply, nbHol, evalC_holIncl]
  rw [← nbH_map_eval v]; rfl

theorem nbAnti_map_evalC (v : Lw n → ℂ) :
    (nbAnti (n := n)).map (fun P => evalC P v) = (nbMat v).map (starRingEnd ℂ) := by
  ext a b
  simp only [Matrix.map_apply, nbAnti, nbH_apply, map_add, nbMat, lowMat, Matrix.add_apply,
    Matrix.of_apply, Matrix.one_apply]
  split_ifs <;> simp [evalC, antiIncl, coord]

/-- The evaluation at a point, as a ring hom. -/
def evalAt (v : Lw n → ℂ) : R2 n →+* ℂ := (eval fun c => coord (Lw n) c v : R2 n →+* ℂ)

theorem evalAt_apply (v : Lw n → ℂ) (P : R2 n) : evalAt v P = evalC P v := rfl

theorem evalC_gramF (m : Fin n) (v : Lw n → ℂ) : evalC (gramF m) v = gramWeight m v := by
  rw [← evalAt_apply, gramF, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul,
    Matrix.transpose_map, ← Matrix.submatrix_map, ← Matrix.submatrix_map]
  have h1 : (nbHol (n := n)).map (evalAt v) = nbMat v := nbHol_map_evalC v
  have h2 : (nbAnti (n := n)).map (evalAt v) = (nbMat v).map (starRingEnd ℂ) := nbAnti_map_evalC v
  rw [h1, h2, AdjacentGrowth.gramWeight, tailGram]
  rfl

theorem holPart_nbHol : (nbHol (n := n)).map holPart = nbH := by
  ext a b
  simp [nbHol, holPart_holIncl]

theorem holPart_nbAnti : (nbAnti (n := n)).map holPart = 1 := by
  ext a b
  simp only [Matrix.map_apply, nbAnti, nbH_apply, map_add, Matrix.one_apply]
  split_ifs <;> simp [antiIncl, holPart]

theorem det_nbH_submatrix (m : Fin n) :
    ((nbH (n := n)).submatrix (Subtype.val : Tail n m → Fin n) Subtype.val).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · refine Finset.prod_eq_one fun a _ => ?_
    simp [nbH_apply]
  · intro a b hab
    have hab' : (a : Fin n) < b := hab
    simp only [Matrix.submatrix_apply, nbH_apply, ite_eq_right (ne_of_lt hab'),
      dite_eq_right (not_lt.2 hab'.le), add_zero]

theorem holPart_gramF (m : Fin n) : holPart (gramF m) = 1 := by
  rw [gramF, ← AlgHom.coe_toRingHom, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul,
    Matrix.transpose_map, ← Matrix.submatrix_map, ← Matrix.submatrix_map]
  simp only [AlgHom.coe_toRingHom]
  rw [holPart_nbHol, holPart_nbAnti, Matrix.transpose_submatrix, Matrix.transpose_one,
    ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.mul_one]
  exact det_nbH_submatrix m

/-- `D = ∏_m T_m`, formally. -/
def gramProdF : R2 n := ∏ m, gramF m

theorem evalC_gramProdF (v : Lw n → ℂ) :
    evalC (gramProdF (n := n)) v = ∏ m, gramWeight m v := by
  rw [← evalAt_apply, gramProdF, map_prod]
  exact Finset.prod_congr rfl fun m _ => evalC_gramF m v

theorem holPart_gramProdF : holPart (gramProdF (n := n)) = 1 := by
  rw [gramProdF, map_prod]
  exact Finset.prod_eq_one fun m _ => holPart_gramF m

/-! ## Jets -/

variable (σ : Fin n → ℂ)

/-- `F(nbUnit v) D(v)^N = ω(v) P(v, v̄)`. -/
def JetRel (F : Langlands.GeneralLinear n ℂ → ℂ) (N : ℕ) (P : R2 n) : Prop :=
  ∀ v, F (nbUnit v) * (∏ m, gramWeight m v) ^ N = (∏ m, gramWeight m v ^ σ m) * evalC P v

/-- `F` has the holomorphic jet `Q`. -/
def HasJet (F : Langlands.GeneralLinear n ℂ → ℂ) (Q : Pol n) : Prop :=
  ∃ N P, JetRel σ F N P ∧ ιP (holPart P) = Q

variable {σ}

theorem JetRel.lift {F : Langlands.GeneralLinear n ℂ → ℂ} {N : ℕ} {P : R2 n}
    (h : JetRel σ F N P) (k : ℕ) : JetRel σ F (N + k) (P * gramProdF ^ k) := by
  intro v
  have hD : evalC (gramProdF ^ k) v = (∏ m, gramWeight m v) ^ k := by
    rw [← evalAt_apply, map_pow, evalAt_apply, evalC_gramProdF]
  rw [pow_add, ← mul_assoc, h v, evalC_mul, hD]
  ring

theorem holPart_lift (P : R2 n) (k : ℕ) : holPart (P * gramProdF ^ k) = holPart P := by
  rw [map_mul, map_pow, holPart_gramProdF, one_pow, mul_one]

theorem HasJet.unique {F : Langlands.GeneralLinear n ℂ → ℂ} {Q₁ Q₂ : Pol n}
    (h₁ : HasJet σ F Q₁) (h₂ : HasJet σ F Q₂) : Q₁ = Q₂ := by
  obtain ⟨N₁, P₁, hP₁, rfl⟩ := h₁
  obtain ⟨N₂, P₂, hP₂, rfl⟩ := h₂
  have e₁ := hP₁.lift N₂
  have e₂ : JetRel σ F (N₁ + N₂) (P₂ * gramProdF ^ N₁) := by
    have := hP₂.lift N₁; rwa [add_comm N₂] at this
  have hAB : P₁ * gramProdF ^ N₂ = P₂ * gramProdF ^ N₁ := by
    rw [← sub_eq_zero]
    refine evalC_injective fun v => ?_
    have hω := weight_ne_zero gramWeight σ isPosReal_gramWeight v
    have h := (e₁ v).symm.trans (e₂ v)
    rw [← evalAt_apply, map_sub, evalAt_apply, evalAt_apply, mul_left_cancel₀ hω h, sub_self]
  rw [← holPart_lift P₁ N₂, hAB, holPart_lift]

theorem HasJet.add {F G : Langlands.GeneralLinear n ℂ → ℂ} {Q Q' : Pol n}
    (hF : HasJet σ F Q) (hG : HasJet σ G Q') : HasJet σ (F + G) (Q + Q') := by
  obtain ⟨N₁, P₁, h₁, rfl⟩ := hF
  obtain ⟨N₂, P₂, h₂, rfl⟩ := hG
  refine ⟨N₁ + N₂, P₁ * gramProdF ^ N₂ + P₂ * gramProdF ^ N₁, fun v => ?_, ?_⟩
  · have e₁ := h₁.lift N₂ v
    have e₂ : G (nbUnit v) * (∏ m, gramWeight m v) ^ (N₁ + N₂) =
        (∏ m, gramWeight m v ^ σ m) * evalC (P₂ * gramProdF ^ N₁) v := by
      have := h₂.lift N₁ v; rwa [add_comm N₂] at this
    rw [Pi.add_apply, add_mul, e₁, e₂, evalC_add]
    ring
  · rw [map_add, holPart_lift, holPart_lift, map_add]

theorem HasJet.smul (c : ℂ) {F : Langlands.GeneralLinear n ℂ → ℂ} {Q : Pol n}
    (hF : HasJet σ F Q) : HasJet σ (c • F) (c • Q) := by
  obtain ⟨N, P, h, rfl⟩ := hF
  refine ⟨N, C c * P, fun v => ?_, ?_⟩
  · rw [Pi.smul_apply, smul_eq_mul, mul_assoc, h v, evalC_mul, evalC_C]
    ring
  · rw [map_mul, map_mul, smul_eq_C_mul]
    simp [holPart]

theorem hasJet_zero : HasJet σ (0 : Langlands.GeneralLinear n ℂ → ℂ) 0 :=
  ⟨0, 0, fun v => by simp [evalC], by simp⟩

theorem HasJet.sum {ι : Type*} (s : Finset ι) (F : ι → Langlands.GeneralLinear n ℂ → ℂ)
    (Q : ι → Pol n) (h : ∀ i ∈ s, HasJet σ (F i) (Q i)) :
    HasJet σ (∑ i ∈ s, F i) (∑ i ∈ s, Q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasJet_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end Langlands.Archimedean.HolomorphicJets
