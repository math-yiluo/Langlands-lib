/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import Mathlib.Topology.Instances.Matrix
import WeilConjectures.LinearAlgebra.ContinuousIntegralDiagonalRankLocus
import WeilConjectures.LinearAlgebra.DvrMatrixSmithPowers

/-!
# Local continuous Smith reduction of integral matrices

Source: Hemo--Richarz--Scholbach, arXiv:2305.18131, Example 3.1 and the proof of
Theorem 6.12(2), finite coefficient extension case. The local constant-cokernel-type
Smith variant is the agent argument recorded in the blueprint, rather than a verbatim HRS theorem
(auxiliary; not a blueprint node).

The valuation topology on the integer ring is its maximal-ideal-adic topology.
The cokernels below are ordinary algebraic module quotients, with no sheaf structure.
-/

@[expose] public section

universe u v

namespace Padic

private theorem matrix_rank_eq_of_cokernel_equiv
    {A : Type u} [CommRing A] [IsDomain A] {m n : ℕ}
    (F G : Matrix (Fin n) (Fin m) A)
    (h : Nonempty (((Fin n → A) ⧸ LinearMap.range F.mulVecLin) ≃ₗ[A]
      ((Fin n → A) ⧸ LinearMap.range G.mulVecLin))) : F.rank = G.rank := by
  obtain ⟨h⟩ := h
  have hF := (LinearMap.range F.mulVecLin).finrank_quotient_add_finrank
  have hG := (LinearMap.range G.mulVecLin).finrank_quotient_add_finrank
  rw [h.finrank_eq] at hF
  exact Nat.add_left_cancel (hF.trans hG.symm)

/-- Continuous integral matrices with locally constant scalar cokernel type admit a local
Smith reduction by integral invertible matrices whose entries and inverse entries are
continuous. The open cover is indexed by the points, each point lying in its own member.
The fixed rectangular diagonal on each member has increasing nonnegative uniformizer
exponents, including exponent zero, and can have no nonzero entries.

Source: Hemo--Richarz--Scholbach, arXiv:2305.18131, Example 3.1 and the continuous integral
pivot/division argument of Theorem 6.12(2); agent local constant-type Smith variant
(auxiliary; not a blueprint node).

Proof: Choose a type-constant open neighbourhood of each point. Scalar Smith form
at the central point supplies constant invertible factors and a sorted diagonal D.
The quotient-plus-range finrank formula shows that equivalent cokernels imply equal
matrix ranks. After conjugating by the scalar Smith factors, the family equals D at
its centre and its ranks are bounded by the number of nonzero entries of D. Apply
continuous_integral_diagonal_rank_locus to this family. Transport its neighbourhood
through the open subtype inclusion and compose the continuous factors with the
constant scalar factors. Inverses reverse these products and remain continuous.
Finally choose the resulting neighbourhood at every point. Empty dimensions and
rank zero are covered by the scalar and rank-locus statements. -/
theorem continuous_integral_matrix_local_smith
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (π : coefficientExtensionIntegers l E)
    (hπ : Ideal.span ({π} : Set (coefficientExtensionIntegers l E)) =
      coefficientExtensionMaximalIdeal l E)
    (Y : Type v) [TopologicalSpace Y] (m n : ℕ)
    (F : Y → Matrix (Fin n) (Fin m) (coefficientExtensionIntegers l E))
    (hF : ∀ (i : Fin n) (j : Fin m),
      @Continuous Y (coefficientExtensionIntegers l E) _
        (coefficientExtensionMaximalIdeal l E).adicTopology (fun y ↦ F y i j))
    (h_type : ∀ y : Y, ∃ W : TopologicalSpace.Opens Y, y ∈ W ∧
      ∀ z ∈ W, Nonempty
        (((Fin n → coefficientExtensionIntegers l E) ⧸ LinearMap.range (F z).mulVecLin) ≃ₗ[
          coefficientExtensionIntegers l E]
        ((Fin n → coefficientExtensionIntegers l E) ⧸ LinearMap.range (F y).mulVecLin))) :
    ∃ W : Y → TopologicalSpace.Opens Y, (∀ y : Y, y ∈ W y) ∧
      ∀ y : Y, ∃
        (L : W y → Matrix.GeneralLinearGroup (Fin n) (coefficientExtensionIntegers l E))
        (R : W y → Matrix.GeneralLinearGroup (Fin m) (coefficientExtensionIntegers l E))
        (r : ℕ) (_hr : r ≤ min m n) (e : Fin r → ℕ)
        (D : Matrix (Fin n) (Fin m) (coefficientExtensionIntegers l E)),
        Monotone e ∧
        (∀ (i : Fin n) (j : Fin m),
          D i j = if h : i.val = j.val ∧ i.val < r then π ^ e ⟨i.val, h.2⟩ else 0) ∧
        (∀ (i j : Fin n),
          @Continuous (W y) (coefficientExtensionIntegers l E) _
            (coefficientExtensionMaximalIdeal l E).adicTopology (fun z ↦ L z i j)) ∧
        (∀ (i j : Fin n),
          @Continuous (W y) (coefficientExtensionIntegers l E) _
            (coefficientExtensionMaximalIdeal l E).adicTopology (fun z ↦ (L z)⁻¹ i j)) ∧
        (∀ (i j : Fin m),
          @Continuous (W y) (coefficientExtensionIntegers l E) _
            (coefficientExtensionMaximalIdeal l E).adicTopology (fun z ↦ R z i j)) ∧
        (∀ (i j : Fin m),
          @Continuous (W y) (coefficientExtensionIntegers l E) _
            (coefficientExtensionMaximalIdeal l E).adicTopology (fun z ↦ (R z)⁻¹ i j)) ∧
        ∀ z : W y,
          (L z : Matrix (Fin n) (Fin n) (coefficientExtensionIntegers l E)) * F z.val *
            (R z : Matrix (Fin m) (Fin m) (coefficientExtensionIntegers l E)) = D := by
  classical
  let A := coefficientExtensionIntegers l E
  let : TopologicalSpace A := (coefficientExtensionMaximalIdeal l E).adicTopology
  have hcoeff := (coefficientExtensionIntegers_dvr l E).choose_spec
  let : IsLocalRing A := hcoeff.2.2.2.1
  let : IsDiscreteValuationRing A := hcoeff.2.2.2.2.2.2.2.1
  have hmax : IsLocalRing.maximalIdeal A = coefficientExtensionMaximalIdeal l E :=
    hcoeff.2.2.2.2.2.1 _ (IsLocalRing.maximalIdeal.isMaximal A)
  have hgen : IsLocalRing.maximalIdeal A = Ideal.span {π} := hmax.trans hπ.symm
  let : IsTopologicalRing A :=
    (coefficientExtensionMaximalIdeal l E).ringFilterBasis.isTopologicalRing
  have hlocal (y : Y) : ∃ W : TopologicalSpace.Opens Y, y ∈ W ∧
      ∃ (L : W → Matrix.GeneralLinearGroup (Fin n) A)
        (R : W → Matrix.GeneralLinearGroup (Fin m) A)
        (r : ℕ) (_hr : r ≤ min m n) (e : Fin r → ℕ) (D : Matrix (Fin n) (Fin m) A),
        Monotone e ∧
        (∀ (i : Fin n) (j : Fin m),
          D i j = if h : i.val = j.val ∧ i.val < r then π ^ e ⟨i.val, h.2⟩ else 0) ∧
        (∀ i j : Fin n, Continuous (fun z ↦ L z i j)) ∧
        (∀ i j : Fin n, Continuous (fun z ↦ (L z)⁻¹ i j)) ∧
        (∀ i j : Fin m, Continuous (fun z ↦ R z i j)) ∧
        (∀ i j : Fin m, Continuous (fun z ↦ (R z)⁻¹ i j)) ∧
        ∀ z : W, (L z : Matrix (Fin n) (Fin n) A) * F z.val *
          (R z : Matrix (Fin m) (Fin m) A) = D := by
    obtain ⟨V, hyV, hV⟩ := h_type y
    obtain ⟨L₀, R₀, r, hr, e, D, he, hD, hrank, hsmith⟩ :=
      Matrix.exists_smith_pow π hgen m n (F y)
    let G : V → Matrix (Fin n) (Fin m) A := fun z ↦
      (L₀ : Matrix (Fin n) (Fin n) A) * F z.val * (R₀ : Matrix (Fin m) (Fin m) A)
    have hG : ∀ i j, Continuous (fun z : V ↦ G z i j) := by
      have hFV : Continuous (fun z : V ↦ F z.val) :=
        (continuous_matrix hF).comp continuous_subtype_val
      exact fun i j ↦ ((continuous_const.matrix_mul hFV).matrix_mul
        continuous_const).matrix_elem i j
    have hGrank (z : V) : (G z).rank ≤ r := by
      calc
        (G z).rank ≤ (F z.val).rank :=
          (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
        _ = (F y).rank := matrix_rank_eq_of_cokernel_equiv _ _ (hV z.val z.property)
        _ = r := hrank.symm
    obtain ⟨U, hyU, L, R, hL, hLi, hR, hRi, hred⟩ :=
      continuous_integral_diagonal_rank_locus l E π hπ V m n r hr e he D hD G hG
        ⟨y, hyV⟩ hsmith hGrank
    let W : TopologicalSpace.Opens Y :=
      ⟨Subtype.val '' (U : Set V), V.isOpen.isOpenMap_subtype_val _ U.isOpen⟩
    have hmem (z : W) : z.val ∈ V ∧ (⟨z.val, by
        obtain ⟨w, _, hw⟩ := z.property
        exact hw ▸ w.property⟩ : V) ∈ U := by
      obtain ⟨w, hwU, hw⟩ := z.property
      have hz : (w : Y) = z := hw
      refine ⟨by simpa only [hz] using w.property, ?_⟩
      have heq : w = (⟨z.val, by simpa only [hz] using w.property⟩ : V) :=
        Subtype.ext hw
      exact heq ▸ hwU
    let k : W → U := fun z ↦ ⟨⟨z.val, (hmem z).1⟩, (hmem z).2⟩
    have hk : Continuous k :=
      (continuous_subtype_val.subtype_mk _).subtype_mk _
    refine ⟨W, ⟨⟨y, hyV⟩, hyU, rfl⟩,
      (fun z ↦ L (k z) * L₀), (fun z ↦ R₀ * R (k z)),
      r, hr, e, D, he, hD, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun i j ↦ ((continuous_matrix (fun i j ↦ (hL i j).comp hk)).matrix_mul
        continuous_const).matrix_elem i j
    · intro i j
      have hc : Continuous (fun z : W ↦
          (↑((L (k z))⁻¹) : Matrix (Fin n) (Fin n) A)) :=
        continuous_matrix (fun i j ↦ (hLi i j).comp hk)
      simpa only [mul_inv_rev, Units.val_mul] using
        ((continuous_const : Continuous (fun _ : W ↦
          (↑(L₀⁻¹) : Matrix (Fin n) (Fin n) A))).matrix_mul hc).matrix_elem i j
    · exact fun i j ↦ (continuous_const.matrix_mul
        (continuous_matrix (fun i j ↦ (hR i j).comp hk))).matrix_elem i j
    · intro i j
      have hc : Continuous (fun z : W ↦
          (↑((R (k z))⁻¹) : Matrix (Fin m) (Fin m) A)) :=
        continuous_matrix (fun i j ↦ (hRi i j).comp hk)
      simpa only [mul_inv_rev, Units.val_mul] using
        (hc.matrix_mul (continuous_const : Continuous (fun _ : W ↦
          (↑(R₀⁻¹) : Matrix (Fin m) (Fin m) A)))).matrix_elem i j
    · intro z
      simpa only [Units.val_mul, Matrix.mul_assoc, G, k] using hred (k z)
  choose W hW hred using hlocal
  exact ⟨W, hW, hred⟩

end Padic
