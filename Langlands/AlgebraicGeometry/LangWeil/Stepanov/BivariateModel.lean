import Langlands.AlgebraicGeometry.LangWeil.PlaneCurveLinearFibres
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# From `MvPolynomial (Fin 2) F` to nested polynomials `F[X][Y]`

The algebra isomorphism `Polynomial.Bivariate.equivMvPolynomial F : F[X][Y] ≃ₐ[F] F[X₀, X₁]`
sends `C X ↦ X₀` and `Y ↦ X₁`. Write `fh` for the preimage of `f`. This file transfers degrees,
irreducibility, the `Y`-derivative, scalar extension and the zero sets of the vertical fibres
between `f` and `fh`.
-/

noncomputable section

universe u

open Polynomial

namespace Langlands.AlgebraicGeometry.LangWeil.Stepanov

section Ring

variable {R : Type u} [CommRing R]

local notation "eqv" => Polynomial.Bivariate.equivMvPolynomial

theorem single_add_single_eq_iff (i j i' j' : ℕ) :
    Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j =
        Finsupp.single (0 : Fin 2) i' + Finsupp.single 1 j' ↔ i = i' ∧ j = j' := by
  constructor
  · intro h
    have h0 := congrArg (fun s : Fin 2 →₀ ℕ => s 0) h
    have h1 := congrArg (fun s : Fin 2 →₀ ℕ => s 1) h
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply] at h0 h1
    simp only [Fin.isValue, ↓reduceIte, zero_ne_one, one_ne_zero, add_zero, zero_add] at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem eq_single_add_single (s : Fin 2 →₀ ℕ) :
    s = Finsupp.single (0 : Fin 2) (s 0) + Finsupp.single 1 (s 1) := by
  ext k
  fin_cases k <;> simp

/-- Coefficients of the image of a nested polynomial under `equivMvPolynomial`. -/
theorem coeff_equivMvPolynomial (g : R[X][X]) (i j : ℕ) :
    (eqv R g).coeff (Finsupp.single 0 i + Finsupp.single 1 j) = (g.coeff j).coeff i := by
  classical
  induction g using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add (eqv R) p q, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, coeff_add,
      coeff_add]
  | monomial n p =>
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [map_add (monomial n) p q, map_add (eqv R), AddMonoidAlgebra.coeff_add,
        Finsupp.add_apply, hp, hq, coeff_add, coeff_add]
    | monomial m a =>
      have h : eqv R (monomial n (monomial m a)) =
          MvPolynomial.monomial (Finsupp.single 0 m + Finsupp.single 1 n) a := by
        rw [← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial, map_mul, map_pow,
          C_mul, map_mul, map_pow, Polynomial.Bivariate.equivMvPolynomial_X,
          Polynomial.Bivariate.equivMvPolynomial_C_C, map_pow,
          Polynomial.Bivariate.equivMvPolynomial_C_X, MvPolynomial.monomial_add_single,
          ← MvPolynomial.C_mul_X_pow_eq_monomial]
      rw [h, MvPolynomial.coeff_monomial, coeff_monomial]
      by_cases hn : n = j <;> by_cases hm : m = i <;>
        simp [hn, hm, coeff_monomial, single_add_single_eq_iff,
          (Finsupp.single_injective (M := ℕ) (0 : Fin 2)).eq_iff,
          (Finsupp.single_injective (M := ℕ) (1 : Fin 2)).eq_iff]

theorem coeff_coeff_equivMvPolynomial_symm (f : MvPolynomial (Fin 2) R) (i j : ℕ) :
    (((eqv R).symm f).coeff j).coeff i = f.coeff (Finsupp.single 0 i + Finsupp.single 1 j) := by
  rw [← coeff_equivMvPolynomial, AlgEquiv.apply_symm_apply]

theorem natDegree_equivMvPolynomial_symm (f : MvPolynomial (Fin 2) R) :
    ((eqv R).symm f).natDegree = f.degreeOf 1 := by
  classical
  apply le_antisymm
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    ext i
    rw [coeff_coeff_equivMvPolynomial_symm, coeff_zero]
    by_contra hc
    have hle := MvPolynomial.monomial_le_degreeOf 1 (MvPolynomial.mem_support_iff.mpr hc)
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply, Fin.isValue,
      zero_ne_one, ↓reduceIte, zero_add] at hle
    exact absurd hle (by omega)
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro s hs
    apply le_natDegree_of_ne_zero
    intro hz
    have h := coeff_coeff_equivMvPolynomial_symm f (s 0) (s 1)
    rw [hz, coeff_zero, ← eq_single_add_single] at h
    exact MvPolynomial.mem_support_iff.mp hs h.symm

theorem natDegree_coeff_equivMvPolynomial_symm_le (f : MvPolynomial (Fin 2) R) (j : ℕ) :
    (((eqv R).symm f).coeff j).natDegree ≤ f.degreeOf 0 := by
  classical
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [coeff_coeff_equivMvPolynomial_symm]
  by_contra hc
  have hle := MvPolynomial.monomial_le_degreeOf 0 (MvPolynomial.mem_support_iff.mpr hc)
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply, Fin.isValue,
    one_ne_zero, ↓reduceIte, add_zero] at hle
  exact absurd hle (by omega)

theorem equivMvPolynomial_symm_map {S : Type u} [CommRing S] (φ : R →+* S)
    (f : MvPolynomial (Fin 2) R) :
    (eqv S).symm (MvPolynomial.map φ f) = ((eqv R).symm f).map (Polynomial.mapRingHom φ) := by
  ext j i
  rw [coeff_coeff_equivMvPolynomial_symm, coeff_map, coe_mapRingHom, coeff_map,
    coeff_coeff_equivMvPolynomial_symm, MvPolynomial.coeff_map]

theorem derivative_equivMvPolynomial_symm (f : MvPolynomial (Fin 2) R) :
    eqv R (derivative ((eqv R).symm f)) = MvPolynomial.pderiv 1 f := by
  rw [← Polynomial.Bivariate.pderiv_one_equivMvPolynomial, AlgEquiv.apply_symm_apply]

theorem eval_equivMvPolynomial (g : R[X][X]) (x y : R) :
    MvPolynomial.eval ![x, y] (eqv R g) = (g.map (Polynomial.evalRingHom x)).eval y := by
  have h : (MvPolynomial.eval ![x, y]).comp (eqv R).toRingEquiv.toRingHom =
      (Polynomial.evalRingHom y).comp (Polynomial.mapRingHom (Polynomial.evalRingHom x)) := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext'
      · ext a
        simp
      · simp
    · simp
  exact congrArg (fun φ : R[X][X] →+* R => φ g) h

end Ring

section Field

variable {F : Type u} [Field F]

local notation "eqv" => Polynomial.Bivariate.equivMvPolynomial

/-- A nested polynomial of positive `Y`-degree that is irreducible does not vanish
identically on a vertical line. -/
theorem map_evalRingHom_ne_zero_of_irreducible (P : F[X][X]) (hirr : Irreducible P)
    (hn : 1 ≤ P.natDegree) (x : F) : P.map (Polynomial.evalRingHom x) ≠ 0 := by
  intro hz
  have hdvd : Polynomial.C (X - Polynomial.C x) ∣ P := by
    apply (Polynomial.C_dvd_iff_dvd_coeff _ P).mpr
    intro i
    apply dvd_iff_isRoot.mpr
    have h := congrArg (fun Q : F[X] => Q.coeff i) hz
    simpa only [coeff_map, coeff_zero, coe_evalRingHom, IsRoot.def] using h
  obtain ⟨Q, hQ⟩ := hdvd
  rcases hirr.isUnit_or_isUnit hQ with h | h
  · have h' := (Polynomial.isUnit_C.mp h)
    have := natDegree_eq_zero_of_isUnit h'
    rw [natDegree_X_sub_C] at this
    exact one_ne_zero this
  · have hdeg := natDegree_C_mul_le (X - Polynomial.C x) Q
    rw [← hQ, natDegree_eq_zero_of_isUnit h] at hdeg
    omega

theorem card_zeros_eq_card_roots (f : MvPolynomial (Fin 2) F) (x : F)
    (hQ : ((eqv F).symm f).map (Polynomial.evalRingHom x) ≠ 0) [DecidableEq F] :
    Nat.card {y : F // MvPolynomial.eval ![x, y] f = 0} =
      (((eqv F).symm f).map (Polynomial.evalRingHom x)).roots.toFinset.card := by
  rw [← Nat.card_eq_finsetCard]
  apply Nat.card_congr
  refine Equiv.subtypeEquivRight fun y => ?_
  rw [Multiset.mem_toFinset, mem_roots hQ, IsRoot.def, ← eval_equivMvPolynomial,
    AlgEquiv.apply_symm_apply]

open Classical in
/-- Passage from `f : MvPolynomial (Fin 2) F` to the nested form `fh : F[X][Y]`. -/
def BivariateModel : Prop :=
  ∀ (F : Type u) [Field F] (f : MvPolynomial (Fin 2) F),
    Irreducible (MvPolynomial.map (algebraMap F (AlgebraicClosure F)) f) →
    MvPolynomial.pderiv 1 f ≠ 0 → 1 ≤ f.degreeOf 1 →
    let fh := (Polynomial.Bivariate.equivMvPolynomial F).symm f
    fh.natDegree = f.degreeOf 1 ∧
    (∀ i, (fh.coeff i).natDegree ≤ f.degreeOf 0) ∧
    Irreducible fh ∧
    Irreducible (fh.map (Polynomial.mapRingHom (algebraMap F (AlgebraicClosure F)))) ∧
    Polynomial.derivative fh ≠ 0 ∧
    ∀ x : F, fh.map (Polynomial.evalRingHom x) ≠ 0 ∧
      Nat.card {y : F // MvPolynomial.eval ![x, y] f = 0} =
        (fh.map (Polynomial.evalRingHom x)).roots.toFinset.card

theorem bivariateModel : BivariateModel.{u} := by
  intro F _ f habs hder hn
  dsimp only
  have hirr : Irreducible ((eqv F).symm f) :=
    (MulEquiv.irreducible_iff (eqv F).symm.toMulEquiv).mpr
      (planeCurve_irreducible_of_absolute f habs)
  have hdeg := natDegree_equivMvPolynomial_symm f
  have hfib : ∀ x : F, ((eqv F).symm f).map (Polynomial.evalRingHom x) ≠ 0 :=
    map_evalRingHom_ne_zero_of_irreducible _ hirr (by omega)
  refine ⟨hdeg, natDegree_coeff_equivMvPolynomial_symm_le f, hirr, ?_, ?_, fun x =>
    ⟨hfib x, by classical exact card_zeros_eq_card_roots f x (hfib x)⟩⟩
  · rw [← equivMvPolynomial_symm_map]
    exact (MulEquiv.irreducible_iff (eqv _).symm.toMulEquiv).mpr habs
  · intro hz
    apply hder
    rw [← derivative_equivMvPolynomial_symm, hz, map_zero]

end Field

end Langlands.AlgebraicGeometry.LangWeil.Stepanov
