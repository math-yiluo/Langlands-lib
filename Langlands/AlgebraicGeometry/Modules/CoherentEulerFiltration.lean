import Langlands.AlgebraicGeometry.Modules.CoherentEulerPolynomialAdditivity
import Langlands.AlgebraicGeometry.Modules.ClosedSupportDimension
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Coherent filtrations and Euler polynomial telescoping -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

/-- A finite filtration starting at zero, with chosen coherent graded pieces
and actual short exact sequences between consecutive terms. -/
structure CoherentFiltration (X : Scheme.{u}) (n : ℕ) where
  term : Fin (n + 1) → X.Modules
  factor : Fin n → X.Modules
  zero : IsZero (term 0)
  inclusion : ∀ j : Fin n, term j.castSucc ⟶ term j.succ
  projection : ∀ j : Fin n, term j.succ ⟶ factor j
  comp_zero : ∀ j, inclusion j ≫ projection j = 0
  shortExact : ∀ j, (ShortComplex.mk (inclusion j) (projection j) (comp_zero j)).ShortExact
  term_quasicoherent : ∀ j, (term j).IsQuasicoherent
  term_finite : ∀ j, HasFiniteAffineSections (term j)
  factor_quasicoherent : ∀ j, (factor j).IsQuasicoherent
  factor_finite : ∀ j, HasFiniteAffineSections (factor j)

namespace CoherentFiltration

variable {X : Scheme.{u}} {n : ℕ} (F : CoherentFiltration X n)

instance (j : Fin (n + 1)) : (F.term j).IsQuasicoherent :=
  F.term_quasicoherent j

instance (j : Fin n) : (F.factor j).IsQuasicoherent :=
  F.factor_quasicoherent j

/-- The actual short complex for one adjacent filtration step. -/
def complex (j : Fin n) : ShortComplex X.Modules :=
  ShortComplex.mk (F.inclusion j) (F.projection j) (F.comp_zero j)

/-- Each chosen adjacent complex is short exact. -/
theorem complex_shortExact (j : Fin n) : (F.complex j).ShortExact :=
  F.shortExact j

/-- Every strict support bound for the final term holds exactly when it holds
for all graded factors, including for a filtration of length zero. -/
theorem hasSupportDimensionLT_iff (e : ℕ) :
    HasSupportDimensionLT (F.term (Fin.last n)) e ↔
      ∀ j, HasSupportDimensionLT (F.factor j) e := by
  have h : ∀ k : Fin (n + 1),
      HasSupportDimensionLT (F.term k) e ↔
        ∀ j : Fin n, j.val < k.val → HasSupportDimensionLT (F.factor j) e := by
    intro k
    induction k using Fin.induction with
    | zero =>
        constructor
        · intro _ j hj
          exact (Nat.not_lt_zero j.val hj).elim
        · intro _
          exact HasSupportDimensionLT.of_isZero F.zero e
    | succ k ih =>
        have hstep :
            HasSupportDimensionLT (F.term k.succ) e ↔
              HasSupportDimensionLT (F.term k.castSucc) e ∧
                HasSupportDimensionLT (F.factor k) e :=
          hasSupportDimensionLT_shortExact_iff (F.complex k) (F.complex_shortExact k) e
        rw [hstep, ih]
        constructor
        · rintro ⟨h, hk⟩ j hj
          by_cases he : j = k
          · simpa only [he] using hk
          · apply h j
            have hne : j.val ≠ k.val := fun hval => he (Fin.ext hval)
            simp only [Fin.val_succ, Fin.val_castSucc] at hj ⊢
            omega
        · intro h
          exact ⟨fun j hj => h j (by
            simp only [Fin.val_succ, Fin.val_castSucc] at hj ⊢
            omega), h k (by simp)⟩
  exact (h (Fin.last n)).trans
    ⟨fun h j => h j j.isLt, fun h j _ => h j⟩

open DerivedSections

variable {K : Type u} [Field K]
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]

/-- Every common Newton truncation telescopes along the actual coherent filtration.
No support bound or ampleness assumption is required. -/
theorem coherentEulerPolynomial_last (L : Picard.LineBundle X) (d : ℕ) :
    coherentEulerPolynomial f (F.term (Fin.last n)) (F.term_finite _) L d =
      ∑ j, coherentEulerPolynomial f (F.factor j) (F.factor_finite j) L d := by
  let P : Fin (n + 1) → Polynomial ℚ :=
    fun k => coherentEulerPolynomial f (F.term k) (F.term_finite k) L d
  let Q : Fin n → Polynomial ℚ :=
    fun j => coherentEulerPolynomial f (F.factor j) (F.factor_finite j) L d
  have h0 : P 0 = 0 :=
    coherentEulerPolynomial_zero f (F.term 0) (F.term_finite 0) L d F.zero
  have hstep (j : Fin n) : P j.succ = P j.castSucc + Q j := by
    let : (F.complex j).X₁.IsQuasicoherent := F.term_quasicoherent j.castSucc
    let : (F.complex j).X₂.IsQuasicoherent := F.term_quasicoherent j.succ
    let : (F.complex j).X₃.IsQuasicoherent := F.factor_quasicoherent j
    exact coherentEulerPolynomial_add f (F.complex j) (F.complex_shortExact j)
      (F.term_finite _) (F.term_finite _) (F.factor_finite j) L d
  have hsum : (∑ j : Fin n, P j.succ) =
      (∑ j : Fin n, P j.castSucc) + P (Fin.last n) := by
    have h := (Fin.sum_univ_succ P).symm.trans (Fin.sum_univ_castSucc P)
    simpa only [h0, zero_add] using h
  change P (Fin.last n) = ∑ j, Q j
  symm
  calc
    ∑ j, Q j = ∑ j : Fin n, (P j.succ - P j.castSucc) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hstep j, add_sub_cancel_left]
    _ = (∑ j : Fin n, P j.succ) - ∑ j : Fin n, P j.castSucc :=
      Finset.sum_sub_distrib _ _
    _ = P (Fin.last n) := by rw [hsum, add_sub_cancel_left]

/-- The telescope transports to any actual sheaf isomorphic to the final term. -/
theorem coherentEulerPolynomial_eq_sum (M : X.Modules) [M.IsQuasicoherent]
    (hM : HasFiniteAffineSections M) (i : F.term (Fin.last n) ≅ M)
    (L : Picard.LineBundle X) (d : ℕ) :
    coherentEulerPolynomial f M hM L d =
      ∑ j, coherentEulerPolynomial f (F.factor j) (F.factor_finite j) L d :=
  (coherentEulerPolynomial_iso f (F.term_finite _) hM L d i).symm.trans
    (F.coherentEulerPolynomial_last f L d)

/-- Each coefficient is the sum of the coefficients of the graded factors. -/
theorem coherentEulerPolynomial_coeff_last (L : Picard.LineBundle X) (d k : ℕ) :
    (coherentEulerPolynomial f (F.term (Fin.last n)) (F.term_finite _) L d).coeff k =
      ∑ j, (coherentEulerPolynomial f (F.factor j) (F.factor_finite j) L d).coeff k := by
  rw [F.coherentEulerPolynomial_last f L d]
  exact Polynomial.finsetSum_coeff _ _ _

/-- Nonnegativity and detection of a strict support bound pass from all factors
to the final term at a fixed coefficient. -/
theorem coherentEulerPolynomial_coeff_nonneg_and_pos_iff
    (L : Picard.LineBundle X) (d : ℕ)
    (hfactor : ∀ j,
      0 ≤ (coherentEulerPolynomial f (F.factor j) (F.factor_finite j) L d).coeff d ∧
      (0 < (coherentEulerPolynomial f (F.factor j) (F.factor_finite j) L d).coeff d ↔
        ¬ HasSupportDimensionLT (F.factor j) d)) :
    0 ≤ (coherentEulerPolynomial f (F.term (Fin.last n)) (F.term_finite _) L d).coeff d ∧
      (0 < (coherentEulerPolynomial f (F.term (Fin.last n)) (F.term_finite _) L d).coeff d ↔
        ¬ HasSupportDimensionLT (F.term (Fin.last n)) d) := by
  rw [F.coherentEulerPolynomial_coeff_last f L d d]
  constructor
  · exact Finset.sum_nonneg (fun j _ => (hfactor j).1)
  · calc
      0 < ∑ j, (coherentEulerPolynomial f (F.factor j) (F.factor_finite j) L d).coeff d ↔
          ∃ j, 0 < (coherentEulerPolynomial f (F.factor j) (F.factor_finite j) L d).coeff d := by
            simpa only [Finset.mem_univ, true_and] using
              (Finset.sum_pos_iff_of_nonneg (s := Finset.univ)
                (fun j _ => (hfactor j).1))
      _ ↔ ∃ j, ¬ HasSupportDimensionLT (F.factor j) d :=
        exists_congr (fun j => (hfactor j).2)
      _ ↔ ¬ HasSupportDimensionLT (F.term (Fin.last n)) d := by
        rw [F.hasSupportDimensionLT_iff d]
        simp only [not_forall]

/-- The fixed-coefficient criterion also transports across an endpoint isomorphism. -/
theorem coherentEulerPolynomial_coeff_nonneg_and_pos_iff_of_iso
    (M : X.Modules) [M.IsQuasicoherent] (hM : HasFiniteAffineSections M)
    (i : F.term (Fin.last n) ≅ M) (L : Picard.LineBundle X) (d : ℕ)
    (hfactor : ∀ j,
      0 ≤ (coherentEulerPolynomial f (F.factor j) (F.factor_finite j) L d).coeff d ∧
      (0 < (coherentEulerPolynomial f (F.factor j) (F.factor_finite j) L d).coeff d ↔
        ¬ HasSupportDimensionLT (F.factor j) d)) :
    0 ≤ (coherentEulerPolynomial f M hM L d).coeff d ∧
      (0 < (coherentEulerPolynomial f M hM L d).coeff d ↔
        ¬ HasSupportDimensionLT M d) := by
  have hi : HasSupportDimensionLT M d ↔ HasSupportDimensionLT (F.term (Fin.last n)) d :=
    ⟨fun h => h.of_iso i.symm, fun h => h.of_iso i⟩
  rw [← coherentEulerPolynomial_iso f (F.term_finite _) hM L d i, hi]
  exact F.coherentEulerPolynomial_coeff_nonneg_and_pos_iff f L d hfactor

end CoherentFiltration

end Langlands.AlgebraicGeometry.Modules
