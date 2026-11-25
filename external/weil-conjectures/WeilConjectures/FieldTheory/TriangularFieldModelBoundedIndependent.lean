/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.TriangularFieldModelEquations
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Algebra
import WeilConjectures.FieldTheory.TriangularFieldModelCoefficientDescent

/-! # Bounded monomial independent for triangular quotients

Source: Stacks Project, Algebra, proofs of Tags 07BV and 08JZ.
-/

@[expose] public section

universe u
namespace FieldTheory

/-- Bounded monomials have no nonzero vanishing expansion.
Source: Stacks Project, Algebra, proofs of Tags 07BV and 08JZ.
(blueprint: lem-weil-pbc-triangular-field-model-bounded-independent).

Proof: First identify the quotient of the first d+1 variables by hT-1 with
D=k[X][1/h], using the localization presentation. Agreement on k[X] determines
psi uniquely, including the inverse of h. Split off the last tower variable,
and identify the simultaneous quotient with the quotient of the previous
stage's polynomial ring by the mapped last monic relation. The universal maps
send each variable to its class; their composites fix every variable and the
coefficient ring. Over a nonzero previous stage, mapping preserves the leading
coefficient one and degree e_i. Uniqueness of remainder upon division by this
monic polynomial says all coefficients of a vanishing bounded expansion in
the last variable vanish. Induction applies the same assertion to their bounded
expansions in earlier variables, giving c(a)=0 for every tuple a. For m=0 this
is injectivity of the localization identification. If h=0 the coefficient ring
is zero. If an e_i=0 the exponent set is empty and every coefficient function
is zero; hence the assertion remains true. No field evaluation is used. -/
theorem triangularFieldModel_bounded_independent
    (k : Type u) [Field k] (d m : ℕ) (h : MvPolynomial (Fin d) k)
    (p : (i : Fin m) → Polynomial (MvPolynomial (Fin (d + 1 + i.val)) k))
    (e : Fin m → ℕ) (hp : ∀ i, (p i).Monic)
    (he : ∀ i, (p i).natDegree = e i)
    (psi : Localization.Away h →ₐ[k]
      (MvPolynomial (Fin (d + 1 + m)) k ⧸
        Ideal.ofList (triangularFieldModelEquations k d m h p)))
    (hpsi : ∀ r : MvPolynomial (Fin d) k,
      psi (algebraMap _ (Localization.Away h) r) = Ideal.Quotient.mk _
        (MvPolynomial.rename (fun j : Fin d ↦
          (⟨j.val, by omega⟩ : Fin (d + 1 + m))) r))
    (c : (((i : Fin m) → Fin (e i)) → Localization.Away h))
    (hc : (∑ a : ((i : Fin m) → Fin (e i)),
        psi (c a) * (∏ i : Fin m,
          (Ideal.Quotient.mk _ (MvPolynomial.X
            (⟨d + 1 + i.val, by omega⟩ : Fin (d + 1 + m)))) ^ (a i).val)) = 0) : c = 0 := by
  classical
  induction m with
  | zero =>
    let D := Localization.Away h
    let y : Fin (d + 1) → D := Fin.snoc
      (fun j : Fin d ↦ algebraMap (MvPolynomial (Fin d) k) D (MvPolynomial.X j))
      (IsLocalization.Away.invSelf h)
    have hbase (r : MvPolynomial (Fin d) k) :
        MvPolynomial.aeval y
          (MvPolynomial.rename (fun j : Fin d ↦
            (⟨j.val, by omega⟩ : Fin (d + 1))) r) = algebraMap _ D r := by
      rw [MvPolynomial.aeval_rename]
      have hy : y ∘ (fun j : Fin d ↦ (⟨j.val, by omega⟩ : Fin (d + 1))) =
          fun j ↦ algebraMap (MvPolynomial (Fin d) k) D (MvPolynomial.X j) := by
        funext j
        change y j.castSucc = _
        dsimp only [y]
        exact Fin.snoc_castSucc _ _ j
      rw [hy]
      have hm : MvPolynomial.aeval
          (fun j : Fin d ↦ algebraMap (MvPolynomial (Fin d) k) D (MvPolynomial.X j)) =
          IsScalarTower.toAlgHom k (MvPolynomial (Fin d) k) D := by
        ext j
        simp
      exact DFunLike.congr_fun hm r
    let I := Ideal.ofList (triangularFieldModelEquations k d 0 h p)
    have hrel : I ≤ RingHom.ker (MvPolynomial.aeval y).toRingHom := by
      apply Ideal.span_le.mpr
      intro q hq
      simp only [triangularFieldModelEquations, List.ofFn_zero, List.mem_cons,
        List.not_mem_nil, or_false] at hq
      change MvPolynomial.aeval y q = 0
      subst q
      simp only [map_sub, map_mul, map_one, hbase, MvPolynomial.aeval_X]
      change algebraMap _ D h * y (Fin.last d) - 1 = 0
      simp only [y, Fin.snoc_last, IsLocalization.Away.mul_invSelf, sub_self]
    let ev : (MvPolynomial (Fin (d + 1)) k ⧸ I) →ₐ[k] D :=
      Ideal.Quotient.liftₐ I (MvPolynomial.aeval y)
        (fun q hq ↦ RingHom.mem_ker.mp (hrel hq))
    have hleft : ev.comp psi = AlgHom.id k D := by
      apply AlgHom.toRingHom_injective
      apply IsLocalization.ringHom_ext (Submonoid.powers h)
      apply RingHom.ext
      intro r
      change ev (psi (algebraMap _ D r)) = algebraMap _ D r
      rw [hpsi]
      exact hbase r
    have hc' : psi (c default) = 0 := by simpa using hc
    funext a
    have ha : a = default := Subsingleton.elim _ _
    rw [ha]
    have heq := congrArg ev hc'
    change (ev.comp psi) (c default) = ev 0 at heq
    rw [hleft, map_zero] at heq
    exact heq
  | succ n ih =>
    let p₀ : (i : Fin n) → Polynomial (MvPolynomial (Fin (d + 1 + i.val)) k) :=
      fun i ↦ p i.castSucc
    let I₀ := Ideal.ofList (triangularFieldModelEquations k d n h p₀)
    let Q₀ := MvPolynomial (Fin (d + 1 + n)) k ⧸ I₀
    let f₀ : MvPolynomial (Fin d) k →ₐ[k] Q₀ :=
      (Ideal.Quotient.mkₐ k I₀).comp (MvPolynomial.rename
        (fun j : Fin d ↦ (⟨j.val, by omega⟩ : Fin (d + 1 + n))))
    have hu : IsUnit (f₀ h) := by
      rw [isUnit_iff_exists_inv]
      refine ⟨Ideal.Quotient.mk I₀ (MvPolynomial.X ⟨d, by omega⟩), ?_⟩
      change Ideal.Quotient.mk I₀
        (MvPolynomial.rename (fun j : Fin d ↦
          (⟨j.val, by omega⟩ : Fin (d + 1 + n))) h) * _ = 1
      rw [← map_mul, ← map_one (Ideal.Quotient.mk I₀),
        Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      apply Ideal.subset_span
      simp [triangularFieldModelEquations]
    let psi₀ : Localization.Away h →ₐ[k] Q₀ := IsLocalization.Away.liftAlgHom h hu
    have hpsi₀ : ∀ r : MvPolynomial (Fin d) k,
        psi₀ (algebraMap _ (Localization.Away h) r) = Ideal.Quotient.mk I₀
          (MvPolynomial.rename (fun j : Fin d ↦
            (⟨j.val, by omega⟩ : Fin (d + 1 + n))) r) := by
      intro r
      simp only [psi₀, IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift_eq]
      rfl
    have hj (j : Fin (e (Fin.last n))) :
        (fun a : (i : Fin n) → Fin (e i.castSucc) ↦ c (Fin.snoc a j)) = 0 := by
      apply ih p₀ (fun i ↦ e i.castSucc) (fun i ↦ hp i.castSucc)
        (fun i ↦ he i.castSucc) psi₀ hpsi₀
      exact triangularFieldModel_coefficient_descent k d n h p e
        (hp (Fin.last n)) (he (Fin.last n)) psi hpsi psi₀ hpsi₀ c hc j
    funext a
    have ha := congrFun (hj (a (Fin.last n))) (Fin.init a)
    simpa only [Fin.snoc_init_self, Pi.zero_apply] using ha

end FieldTheory
