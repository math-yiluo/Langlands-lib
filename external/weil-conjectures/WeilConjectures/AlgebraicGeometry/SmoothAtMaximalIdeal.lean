/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import WeilConjectures.AlgebraicGeometry.MaximalIdealDifferentialCotangentDimension
import WeilConjectures.AlgebraicGeometry.RegularMaximalJacobianPresentation
public import Mathlib.Algebra.Module.SpanRankOperations

/-!
# Smoothness at a maximal ideal from a differential dimension bound

Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 00TS
(blueprint: lem-weil-pbc-smooth-at-maximal-ideal-alg-closed-differentials-bound).
-/

@[expose] public section

universe u v

namespace Algebra

/-- Over an algebraically closed field, the differential dimension bound at a maximal ideal
implies smoothness there. Source: Stacks Project, Algebra, Lemma Tag 00TS, implication
(2) => (4) (blueprint: lem-weil-pbc-smooth-at-maximal-ideal-alg-closed-differentials-bound).

Proof:
1. The closed-point cotangent comparison identifies the differential fibre dimension
   with the cotangent dimension of S_m. Finite type makes S and S_m Noetherian.
   The assumed inequality and Mathlib's cotangent criterion make S_m regular.
2. The regular-point presentation lemma supplies g outside m and a polynomial quotient
   isomorphic to S_g, with an explicit Jacobian minor that is a unit in that quotient.
3. Form the naive pre-submersive presentation with the selected variables. Its Jacobian
   matrix is the transpose of the matrix in step 2, so its determinant is the same unit.
   It is therefore a submersive presentation. Mathlib makes its quotient standard smooth
   and smooth. Transporting smoothness along the algebra isomorphism proves the result. -/
theorem smoothAtMaximalIdeal_of_finrank_differentials_le_krullDim
    (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    [IsAlgClosed k] [Algebra.FiniteType k S]
    (m : Ideal S) (hm : m.IsMaximal)
    (h : ((Module.finrank (m.ResidueField)
      (TensorProduct S m.ResidueField (KaehlerDifferential k S)) : ℕ) : WithBot ℕ∞) ≤
      ringKrullDim (Localization.AtPrime m)) :
    ∃ g : S, g ∉ m ∧ Algebra.Smooth k (Localization.Away g) := by
  classical
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  have hcot := finrank_cotangentSpace_atMaximal_eq_differentials k S m hm
  have hreg : IsRegularLocalRing (Localization.AtPrime m) := by
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, hcot]
    exact h
  obtain ⟨g, hg, n, c, f, e, i, hi, hunit⟩ :=
    exists_jacobian_unit_presentation_of_regularAtMaximal k S m hm hreg
  let P := PreSubmersivePresentation.naive (v := f) i hi.injective
  have hP : IsUnit P.jacobian := by
    rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    have hmatrix : P.jacobiMatrix =
        Matrix.transpose (fun j l : Fin c ↦ MvPolynomial.pderiv (i l) (f j)) := by
      ext j l : 1
      exact PreSubmersivePresentation.jacobiMatrix_naive i hi.injective _ _ j l
    rw [hmatrix, Matrix.det_transpose]
    exact hunit
  let Q : SubmersivePresentation k
      (MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f)) (Fin n) (Fin c) :=
    { toPreSubmersivePresentation := P, jacobian_isUnit := hP }
  have : IsStandardSmooth k (MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f)) :=
    Q.isStandardSmooth
  exact ⟨g, hg, Smooth.of_equiv e⟩

end Algebra
