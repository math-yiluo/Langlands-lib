import Langlands.GroupScheme.MatrixRepresentation.AdditiveDividedPowers

/-! # Ordered products of actual additive subgroup actions -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix Polynomial

namespace Langlands.GroupScheme.MatrixRepresentation.OrderedAdditiveProducts

variable {k : Type u} [Field k] {n : Type} [Fintype n] [DecidableEq n]

/-- Multiply univariate polynomial matrices in order, giving each factor
its own independent variable. -/
def polynomialMatrix : {d : ℕ} → (Fin d → Matrix n n k[X]) →
    Matrix n n (MvPolynomial (Fin d) k)
  | 0, _ => (1 : Matrix n n k).map MvPolynomial.C
  | d + 1, P =>
      (((P 0).map (Polynomial.map MvPolynomial.C)) *
        (polynomialMatrix (fun i => P i.succ)).map Polynomial.C).map
          (MvPolynomial.finSuccEquiv k d).symm

/-- The ordered product of the indicated coefficient matrices. -/
def coefficientProduct : {d : ℕ} → (Fin d → Matrix n n k[X]) →
    (Fin d →₀ ℕ) → Matrix n n k
  | 0, _, _ => 1
  | _ + 1, P, a =>
      Matrix.of (fun i j => (P 0 i j).coeff (a 0)) *
        coefficientProduct (fun i => P i.succ) a.tail

theorem polynomialMatrix_coeff_cons {d : ℕ}
    (P : Fin (d + 1) → Matrix n n k[X]) (a : Fin d →₀ ℕ) (m : ℕ) (i j : n) :
    (polynomialMatrix P i j).coeff (a.cons m) =
      ∑ l, (P 0 i l).coeff m *
        (polynomialMatrix (fun r => P r.succ) l j).coeff a := by
  rw [← MvPolynomial.finSuccEquiv_coeff_coeff]
  simp only [polynomialMatrix, Matrix.map_apply, AlgEquiv.apply_symm_apply,
    Matrix.mul_apply, Polynomial.finsetSum_coeff, Polynomial.coeff_mul_C,
    Polynomial.coeff_map, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]

/-- Each coefficient of the actual ordered polynomial product is the
product of the individual coefficient matrices in precisely the same order. -/
theorem polynomialMatrix_coeff {d : ℕ}
    (P : Fin d → Matrix n n k[X]) (a : Fin d →₀ ℕ) :
    (fun i j => (polynomialMatrix P i j).coeff a) = coefficientProduct P a := by
  induction d with
  | zero =>
    have ha : a = 0 := Subsingleton.elim _ _
    subst a
    ext i j
    simp [polynomialMatrix, coefficientProduct]
  | succ d ih =>
    ext i j
    rw [← Finsupp.cons_tail a, polynomialMatrix_coeff_cons]
    change _ = (Matrix.of (fun i j => (P 0 i j).coeff (a 0)) *
      coefficientProduct (fun r => P r.succ) a.tail) i j
    rw [← ih]
    rfl

private theorem aeval_finSucc_symm {A : Type u} [CommRing A] [Algebra k A]
    {d : ℕ} (t : Fin (d + 1) → A)
    (Q : Polynomial (MvPolynomial (Fin d) k)) :
    MvPolynomial.aeval t ((MvPolynomial.finSuccEquiv k d).symm Q) =
      Polynomial.eval₂ (MvPolynomial.aeval (fun i => t i.succ)).toRingHom (t 0) Q := by
  let F : Polynomial (MvPolynomial (Fin d) k) →ₐ[k] A :=
    Polynomial.eval₂AlgHom (MvPolynomial.aeval (fun i => t i.succ)) (t 0)
      (fun _ => Commute.all _ _)
  have h : MvPolynomial.aeval t =
      F.comp (MvPolynomial.finSuccEquiv k d).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [F, MvPolynomial.finSuccEquiv_X_zero]
    · simp [F, MvPolynomial.finSuccEquiv_X_succ]
  change MvPolynomial.aeval t _ = F Q
  rw [h, AlgHom.comp_apply]
  exact congrArg F ((MvPolynomial.finSuccEquiv k d).apply_symm_apply Q)

/-- The ordered polynomial matrix evaluates over every commutative test algebra. -/
theorem polynomialMatrix_aeval {A : Type u} [CommRing A] [Algebra k A] {d : ℕ}
    (P : Fin d → Matrix n n k[X]) (t : Fin d → A) :
    (polynomialMatrix P).map (MvPolynomial.aeval t) =
      (List.ofFn fun i => (P i).map (Polynomial.aeval (t i))).prod := by
  induction d with
  | zero => simp [polynomialMatrix]
  | succ d ih =>
    rw [List.ofFn_succ, List.prod_cons, ← ih]
    ext i j
    simp only [polynomialMatrix, Matrix.map_apply, aeval_finSucc_symm,
      Matrix.mul_apply, map_sum, map_mul, Polynomial.eval₂_map, Polynomial.eval₂_C]
    apply Finset.sum_congr rfl
    intro l _
    congr 1
    congr 1
    ext c
    exact MvPolynomial.aeval_C _ c

/-- Evaluation over the base field preserves the order of the matrix factors. -/
theorem polynomialMatrix_eval {d : ℕ}
    (P : Fin d → Matrix n n k[X]) (t : Fin d → k) :
    (polynomialMatrix P).map (MvPolynomial.eval t) =
      (List.ofFn fun i => (P i).map (Polynomial.eval (t i))).prod := by
  simpa only [MvPolynomial.aeval_eq_eval, Polynomial.coe_aeval_eq_eval] using
    polynomialMatrix_aeval (A := k) P t

theorem coefficientProduct_eq_prod {d : ℕ}
    (P : Fin d → Matrix n n k[X]) (a : Fin d →₀ ℕ) :
    coefficientProduct P a =
      (List.ofFn fun r => Matrix.of fun i j => (P r i j).coeff (a r)).prod := by
  induction d with
  | zero => simp [coefficientProduct]
  | succ d ih =>
    rw [coefficientProduct, List.ofFn_succ, List.prod_cons, ih]
    rfl

section ActualActions

open AdditiveDividedPowers VectorGroupPolynomial
open Langlands.LinearAlgebra.PolynomialCoefficients

variable {G : GroupScheme (Spec (.of k))} {d : ℕ}
    (ρ : MatrixRepresentation G n)
    (x : Fin d → (VectorGroup.groupScheme (.of k) 1 ⟶ G))

/-- An ordered product of actual additive-subgroup points. -/
def orderedPoint (S : CommAlgCat.{u} k) (t : Fin d → S) :
    (algSpec (.of k)).obj (op S) ⟶ G.X :=
  (List.ofFn fun i =>
    VectorGroup.affinePoint (R := .of k) (d := 1) S (fun _ => t i) ≫
      (x i).hom.hom).prod

/-- The polynomial matrix obtained from the actual restricted representations. -/
def actionPolynomial : Matrix n n (MvPolynomial (Fin d) k) :=
  polynomialMatrix (fun i => univariateMatrix (ρ.restrict (x i)))

/-- Evaluation gives the actual ambient matrix at the ordered subgroup product
over every commutative test algebra, including nonreduced algebras. -/
theorem actionPolynomial_aeval (S : CommAlgCat.{u} k) (t : Fin d → S) :
    (actionPolynomial ρ x).map (MvPolynomial.aeval t) =
      (ρ.affineMatrix S (orderedPoint x S t) : Matrix n n S) := by
  simp only [actionPolynomial, polynomialMatrix_aeval, univariateMatrix_aeval,
    orderedPoint]
  trans (List.ofFn fun i =>
    (ρ.affineMatrix S (VectorGroup.affinePoint (R := .of k) (d := 1) S
      (fun _ => t i) ≫ (x i).hom.hom) : Matrix n n S)).prod
  · apply congrArg List.prod
    apply congrArg List.ofFn
    funext i
    exact congrArg (fun A : GL n S => (A : Matrix n n S))
      (affineMatrix_restrict ρ (x i) S
        (VectorGroup.affinePoint (R := .of k) (d := 1) S (fun _ => t i)))
  · simpa only [List.map_ofFn, Function.comp_def, MonoidHom.comp_apply,
      Units.coeHom_apply] using
        (map_list_prod ((Units.coeHom (Matrix n n S)).comp (ρ.affineMatrix S))
          (List.ofFn fun i =>
            VectorGroup.affinePoint (R := .of k) (d := 1) S (fun _ => t i) ≫
              (x i).hom.hom)).symm

/-- The actual ordered action at a base-field parameter tuple. -/
def orderedOperator (t : Fin d → k) : Module.End k (n → k) :=
  (ρ.affineAction (.of k k) (orderedPoint x (.of k k) t)).toLinearMap

/-- The finite polynomial family of operators of the ordered action. -/
def orderedCoefficients : (Fin d →₀ ℕ) →₀ Module.End k (n → k) :=
  operatorCoefficients (actionPolynomial ρ x)

/-- Evaluation of the operator polynomial is the original action. -/
theorem evaluation_orderedCoefficients (t : Fin d → k) :
    evaluation t (orderedCoefficients ρ x) = orderedOperator ρ x t := by
  rw [orderedCoefficients, evaluation_operatorCoefficients]
  have h := actionPolynomial_aeval ρ x (.of k k) t
  rw [MvPolynomial.aeval_eq_eval] at h
  rw [h]
  rfl

/-- Each operator coefficient is an ordered product of the actual divided powers. -/
theorem orderedCoefficients_eq_prod (a : Fin d →₀ ℕ) :
    orderedCoefficients ρ x a =
      (List.ofFn fun i => dividedPower (ρ.restrict (x i)) (a i)).prod := by
  rw [orderedCoefficients, operatorCoefficients_apply, actionPolynomial,
    polynomialMatrix_coeff, coefficientProduct_eq_prod]
  simp_rw [dividedPower_eq_toLin]
  change Matrix.toLinAlgEquiv' _ =
    (List.ofFn fun r => Matrix.toLinAlgEquiv' (Matrix.of fun i j =>
      (univariateMatrix (ρ.restrict (x r)) i j).coeff (a r))).prod
  simpa only [List.map_ofFn, Function.comp_def] using
    (map_list_prod (Matrix.toLinAlgEquiv' : Matrix n n k ≃ₐ[k] Module.End k (n → k))
      (List.ofFn fun r => Matrix.of fun i j =>
        (univariateMatrix (ρ.restrict (x r)) i j).coeff (a r)))

/-- Over an infinite field, actual ordered point operators and the ordered
divided-power products span the same subspace of endomorphisms. -/
theorem span_range_orderedOperator_eq_span_range_dividedPowers [Infinite k] :
    Submodule.span k (Set.range (orderedOperator ρ x)) =
      Submodule.span k (Set.range fun a : Fin d →₀ ℕ =>
        (List.ofFn fun i => dividedPower (ρ.restrict (x i)) (a i)).prod) := by
  have h := span_range_evaluation_eq_span_range_coefficients (k := k)
    (orderedCoefficients ρ x)
  have hf : ⇑(orderedCoefficients ρ x) =
      fun a => (List.ofFn fun i => dividedPower (ρ.restrict (x i)) (a i)).prod :=
    funext (orderedCoefficients_eq_prod ρ x)
  rw [hf] at h
  simpa only [evaluation_orderedCoefficients] using h

/-- Actual ordered point operators and ordered divided-power products preserve
exactly the same subspaces over an infinite field. -/
theorem invariant_orderedOperator_iff_invariant_dividedPowers [Infinite k]
    (S : Submodule k (n → k)) :
    (∀ t : Fin d → k, ∀ v ∈ S, orderedOperator ρ x t v ∈ S) ↔
      ∀ a : Fin d →₀ ℕ, ∀ v ∈ S,
        ((List.ofFn fun i => dividedPower (ρ.restrict (x i)) (a i)).prod) v ∈ S := by
  simpa only [evaluation_orderedCoefficients, orderedCoefficients_eq_prod] using
    invariant_evaluation_iff_invariant_coefficients (orderedCoefficients ρ x) S

/-- The span of the actual ordered orbit of any vector equals the span of its
images under all ordered divided-power products. -/
theorem span_range_orderedOrbit_eq_span_range_dividedPowers [Infinite k]
    (v : n → k) :
    Submodule.span k (Set.range fun t : Fin d → k => orderedOperator ρ x t v) =
      Submodule.span k (Set.range fun a : Fin d →₀ ℕ =>
        ((List.ofFn fun i => dividedPower (ρ.restrict (x i)) (a i)).prod) v) := by
  have h := span_range_evaluation_eq_span_range_coefficients (k := k)
    ((orderedCoefficients ρ x).mapRange (LinearMap.applyₗ v)
      (map_zero (LinearMap.applyₗ v)))
  have hf : ⇑((orderedCoefficients ρ x).mapRange (LinearMap.applyₗ v)
      (map_zero (LinearMap.applyₗ v))) =
      fun a => ((List.ofFn fun i => dividedPower (ρ.restrict (x i)) (a i)).prod) v := by
    funext a
    exact congrArg (fun f : Module.End k (n → k) => f v) (orderedCoefficients_eq_prod ρ x a)
  rw [hf] at h
  simpa only [← evaluation_apply_linearMap, evaluation_orderedCoefficients] using h

end ActualActions

end Langlands.GroupScheme.MatrixRepresentation.OrderedAdditiveProducts
