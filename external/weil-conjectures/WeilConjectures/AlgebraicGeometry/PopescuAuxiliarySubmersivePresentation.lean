/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.StandardSmooth

/-! Explicit submersive presentation for the Popescu Jacobian localization.

(blueprint: popescu-auxiliary-submersive-presentation)

The presentation is obtained by adjoining an inverse to the localization element and
using the original equations together with the inverse relation.  The selected Jacobian
minor is a unit by the ideal membership hypothesis, so the resulting presentation is
submersive.  This theorem records the explicit finite variable and relation types; its
proof is deferred to the algebraic Jacobian calculation.
-/

@[expose] public section

universe u
open scoped BigOperators
open MvPolynomial
namespace Algebra

/-- Explicit finite presentation for the localized quotient.
(blueprint: popescu-auxiliary-submersive-presentation)

Proof: adjoin an inverse to the localization element, retain the original equations,
and compute the selected Jacobian minor. The ideal membership hypothesis makes that
minor a unit, so the resulting presentation is submersive.
-/
theorem popescu_auxiliary_submersivePresentation
    (R : Type u) [CommRing R] (N c t : ℕ) (hc : c ≤ N)
    (f : Fin c → MvPolynomial (Fin N) R)
    (s : Fin (t + 1) → R) (h : MvPolynomial (Fin N) R)
    (hs : C (s 0) - h * Matrix.det
      (fun i j : Fin c => pderiv (Fin.castLE hc i) (f j)) ∈
        Ideal.span (Set.range f)) :
    Nonempty (SubmersivePresentation R (Localization.Away (Ideal.Quotient.mk
      (Ideal.span (Set.range (fun j : Fin c =>
        rename (fun i : Fin N => i.castSucc.succ) (f j))))
      (X (0 : Fin (N + 2)) * X (Fin.last (N + 1)) * C (∏ j : Fin (t + 1), s j))))
      (Fin (N + 3)) (Fin (c + 1))) := by
  classical
  let e : Fin N → Fin (N + 2) := fun i ↦ i.castSucc.succ
  have he : Function.Injective e := by
    intro i j hij
    exact Fin.ext (by simpa [e] using congrArg Fin.val hij)
  let F : Fin c → MvPolynomial (Fin (N + 2)) R := fun j ↦ rename e (f j)
  let I := Ideal.span (Set.range F)
  let A := MvPolynomial (Fin (N + 2)) R ⧸ I
  let q : MvPolynomial (Fin (N + 2)) R →+* A := Ideal.Quotient.mk I
  let a : A := q (X 0 * X (Fin.last (N + 1)) * C (∏ j, s j))
  let B := Localization.Away a
  let l : A →+* B := algebraMap A B
  let φ : MvPolynomial (Fin N) R →+* B := l.comp (q.comp (rename e).toRingHom)
  let P : PreSubmersivePresentation R A (Fin (N + 2)) (Fin c) :=
    PreSubmersivePresentation.naive (v := F) (fun i ↦ e (Fin.castLE hc i))
      (he.comp (Fin.castLE_injective hc))
  let Q : PreSubmersivePresentation A B Unit Unit :=
    PreSubmersivePresentation.localizationAway B a
  have ha : IsUnit (l a) := IsLocalization.Away.algebraMap_isUnit a
  have hzero : ∀ j, φ (f j) = 0 := by
    intro j
    have hj : q (F j) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span ⟨j, rfl⟩)
    simpa [φ, F, q] using congrArg l hj
  have hker : Ideal.span (Set.range f) ≤ RingHom.ker φ := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact hzero j
  have hrel : φ (C (s 0)) = φ h * φ (Matrix.det
      (fun i j : Fin c ↦ pderiv (Fin.castLE hc i) (f j))) := by
    have hz := hker hs
    change φ (C (s 0) - h * _) = 0 at hz
    simpa only [map_sub, map_mul, sub_eq_zero] using hz
  have hsunit : IsUnit (φ (C (s 0))) := by
    have hp : IsUnit (l (q (C (∏ j, s j)))) := by
      have := ha
      simp only [a, map_mul, IsUnit.mul_iff] at this
      exact this.2
    have hp' : IsUnit (∏ j : Fin (t + 1), φ (C (s j))) := by
      simpa [φ, map_prod] using hp
    exact (IsUnit.prod_univ_iff.mp hp') 0
  have hd : IsUnit (φ (Matrix.det
      (fun i j : Fin c ↦ pderiv (Fin.castLE hc i) (f j)))) := by
    rw [hrel] at hsunit
    exact (IsUnit.mul_iff.mp hsunit).2
  have hm : P.jacobiMatrix = (rename e).mapMatrix
      (fun i j : Fin c ↦ pderiv (Fin.castLE hc i) (f j)) := by
    ext i j : 1
    rw [PreSubmersivePresentation.jacobiMatrix_apply]
    change pderiv (e (Fin.castLE hc i)) (rename e (f j)) =
      rename e (pderiv (Fin.castLE hc i) (f j))
    exact pderiv_rename he (Fin.castLE hc i) (f j)
  have hP : IsUnit (l P.jacobian) := by
    convert hd using 1
    rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    change l (q P.jacobiMatrix.det) = l (q (rename e _))
    rw [hm, ← (rename e).map_det]
  let S : SubmersivePresentation R B (Unit ⊕ Fin (N + 2)) (Unit ⊕ Fin c) :=
    { Q.comp P with
      jacobian_isUnit := by
        rw [PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
          Algebra.smul_def, PreSubmersivePresentation.localizationAway_jacobian]
        exact hP.mul ha }
  let ev : Fin (N + 3) ≃ Unit ⊕ Fin (N + 2) :=
    (finSumFinEquiv (m := N + 2) (n := 1)).symm.trans ((Equiv.sumComm _ _).trans
      (Equiv.sumCongr (Equiv.ofUnique (Fin 1) Unit) (Equiv.refl _)))
  let er : Fin (c + 1) ≃ Unit ⊕ Fin c :=
    (finSumFinEquiv (m := c) (n := 1)).symm.trans ((Equiv.sumComm _ _).trans
      (Equiv.sumCongr (Equiv.ofUnique (Fin 1) Unit) (Equiv.refl _)))
  exact ⟨S.reindex ev er⟩

end Algebra
