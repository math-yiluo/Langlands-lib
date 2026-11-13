import Langlands.AlgebraicGeometry.LangWeil.Stepanov.Assembly
import Langlands.AlgebraicGeometry.LangWeil.Stepanov.GoodSet
import Langlands.AlgebraicGeometry.LangWeil.Stepanov.ParameterArithmetic
import Langlands.AlgebraicGeometry.LangWeil.Stepanov.BivariateModel
import Langlands.AlgebraicGeometry.LangWeil.StepanovNormPolynomialsStatement

/-!
# Proof of `StepanovNormPolynomialsStatement`
-/

noncomputable section

universe u

open Polynomial

namespace Langlands.AlgebraicGeometry.LangWeil.Stepanov

variable {F : Type u} [Field F]

local notation "R2" => Polynomial (Polynomial F)

theorem ev_self_eq (x y : F) (A : R2) : ev x y A = (A.map (Polynomial.evalRingHom x)).eval y := by
  rw [ev_eq, Algebra.algebraMap_self, Polynomial.map_id]

theorem ev_derivative_ne_zero {L : Type*} [Field L] [Algebra F L] (x : F) (y : L) (P : R2)
    (hsep : (P.map (Polynomial.evalRingHom x)).Separable) (hy : ev x y P = 0) :
    ev x y (derivative P) ≠ 0 := by
  rw [ev_eq] at hy ⊢
  rw [← derivative_map, ← derivative_map]
  have h := hsep.map (f := algebraMap F L)
  have := h.aeval_derivative_ne_zero (x := y) (by rw [coe_aeval_eq_eval]; exact hy)
  rwa [coe_aeval_eq_eval] at this

/-- Proof of the Library statement `StepanovNormPolynomialsStatement`: the two auxiliary
polynomials of Stepanov's method in Schmidt's version. -/
theorem stepanovNormPolynomials : StepanovNormPolynomialsStatement.{u} := by
  intro F _ _ f habs _ hd1 hn2 hnm
  dsimp only
  intro M hM hq hMn
  classical
  have := Fintype.ofFinite F
  obtain ⟨hdeg, hcoeff, hirr, habs', hder, hfib⟩ := bivariateModel F f habs hd1 (by omega)
  obtain ⟨a1, a2, a3, a4, a5⟩ := stepanovParameterArithmetic (f.degreeOf 1) (f.degreeOf 0) M (Nat.card F) hn2 hnm hM hq
  have hn1 : 1 ≤ ((Polynomial.Bivariate.equivMvPolynomial F).symm f).natDegree := by omega
  have hm1 : 1 ≤ f.degreeOf 0 := by omega
  have hMq : M ≤ Nat.card F := by nlinarith
  obtain ⟨h₁, h₁0, h₁deg, h₁root⟩ := exists_normPoly_rational
    ((Polynomial.Bivariate.equivMvPolynomial F).symm f) (f.degreeOf 0)
    (Nat.card F / f.degreeOf 1 - f.degreeOf 0 * f.degreeOf 1) ((M + f.degreeOf 0) / f.degreeOf 1) M
    habs' hirr hn1 hm1 hcoeff (by rw [hdeg]; exact a1) hMq (by rw [hdeg]; exact a2)
  obtain ⟨h₂, h₂0, h₂deg, h₂root⟩ := exists_normPoly_nonrational
    ((Polynomial.Bivariate.equivMvPolynomial F).symm f) (f.degreeOf 0)
    (Nat.card F / f.degreeOf 1 - f.degreeOf 0 * f.degreeOf 1)
    ((f.degreeOf 1 - 1) * (M + f.degreeOf 0) / f.degreeOf 1) M
    habs' hirr hn1 hm1 hcoeff (by rw [hdeg]; exact a1) hMq (by rw [hdeg]; exact a3)
  obtain ⟨Δ, hΔ0, hΔdeg, hΔ⟩ := exists_goodSet_discriminant
    ((Polynomial.Bivariate.equivMvPolynomial F).symm f) (f.degreeOf 0) hirr hder hcoeff
  rw [hdeg] at h₁deg h₂deg hΔdeg
  refine ⟨Finset.univ.filter (fun x => Δ.eval x ≠ 0), h₁, h₂, ?_, ?_, h₁0, h₂0, ?_, ?_, ?_⟩
  · -- the good set misses fewer than `2 m n` abscissae
    have hsub : Finset.univ.filter (fun x => ¬ Δ.eval x ≠ 0) ⊆ Δ.roots.toFinset := by
      intro x hx
      rw [Multiset.mem_toFinset, mem_roots hΔ0, IsRoot.def]
      simpa using hx
    have hbad : (Finset.univ.filter (fun x => ¬ Δ.eval x ≠ 0)).card ≤ Δ.natDegree :=
      ((Finset.card_le_card hsub).trans (Multiset.toFinset_card_le _)).trans (card_roots' Δ)
    have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset F))
      (fun x => Δ.eval x ≠ 0)
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at hsplit
    have hlt : (2 * f.degreeOf 1 - 1) * f.degreeOf 0 < 2 * f.degreeOf 0 * f.degreeOf 1 := by
      have h2 : 2 * f.degreeOf 1 - 1 < 2 * f.degreeOf 1 := by omega
      calc (2 * f.degreeOf 1 - 1) * f.degreeOf 0 < 2 * f.degreeOf 1 * f.degreeOf 0 :=
            Nat.mul_lt_mul_of_pos_right h2 (by omega)
        _ = 2 * f.degreeOf 0 * f.degreeOf 1 := by ring
    omega
  · -- at most `n` points on each vertical line
    intro x
    rw [(hfib x).2]
    calc _ ≤ Multiset.card (((Polynomial.Bivariate.equivMvPolynomial F).symm f).map
          (Polynomial.evalRingHom x)).roots := Multiset.toFinset_card_le _
      _ ≤ _ := card_roots' _
      _ ≤ _ := natDegree_map_le
      _ = _ := hdeg
  · calc h₁.natDegree ≤ _ := h₁deg
      _ = _ := by ring
      _ < _ := a4
  · calc h₂.natDegree ≤ _ := h₂deg
      _ = _ := by ring
      _ < _ := a5
  · intro x hx
    have hΔx : Δ.eval x ≠ 0 := (Finset.mem_filter.mp hx).2
    obtain ⟨hdx, hsep⟩ := hΔ x hΔx
    rw [(hfib x).2]
    constructor
    · refine h₁root x _ fun y hy => ?_
      have hy' : ev x y ((Polynomial.Bivariate.equivMvPolynomial F).symm f) = 0 := by
        rw [ev_self_eq]
        exact (mem_roots (hfib x).1).mp (Multiset.mem_toFinset.mp hy)
      exact ⟨hy', ev_derivative_ne_zero x y _ hsep hy'⟩
    · obtain ⟨T, hT, hTcard⟩ := nonrationalRoots F _ hsep
      have hg : ((Polynomial.Bivariate.equivMvPolynomial F).symm f).leadingCoeff.eval x ≠ 0 := by
        have h := leadingCoeff_ne_zero.mpr (hfib x).1
        rwa [leadingCoeff, hdx, coeff_map, coe_evalRingHom] at h
      refine le_trans ?_ (h₂root x T hg fun y hy => ?_)
      · rw [hdx, hdeg] at hTcard
        exact Nat.mul_le_mul_left M hTcard
      · obtain ⟨h1, h2, h3⟩ := hT y hy
        have h1' : ev x y ((Polynomial.Bivariate.equivMvPolynomial F).symm f) = 0 := by
          rw [ev_eq]; exact h1
        refine ⟨h1', ev_derivative_ne_zero x y _ hsep h1', ?_, h3⟩
        rw [ev_eq]; exact h2

end Langlands.AlgebraicGeometry.LangWeil.Stepanov
