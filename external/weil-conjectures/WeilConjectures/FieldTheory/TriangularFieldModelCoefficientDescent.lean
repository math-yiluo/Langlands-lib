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
public import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.Algebra.BigOperators.Fin

/-! # Descent of the last coefficient in a triangular monic quotient

Source: Stacks Project, Algebra, proofs of Tags 07BV and 08JZ.
-/

@[expose] public section

universe u
namespace FieldTheory

/-- Vanishing in a triangular quotient descends to each last-variable coefficient
in the preceding quotient. Earlier relations need not be monic.
Source: Stacks Project, Algebra, proofs of Tags 07BV and 08JZ.
(blueprint: lem-weil-pbc-triangular-field-model-coefficient-descent).

Proof: Let Q₀ be the preceding quotient and g the image of the last polynomial
in Q₀[X]. If Q₀ is zero, every coefficient sum is zero. Otherwise mapping the
last polynomial preserves its monicity and natural degree. Set S = AdjoinRoot g.
Evaluate every preceding variable at its coefficient class in S and the last
variable at root g. The localization equation and every earlier relation vanish
because their preceding quotient classes vanish; the last relation vanishes by
AdjoinRoot.eval₂_root. Thus evaluation descends to a k-algebra map from the full
simultaneous quotient to S. Its composite with psi agrees with of g composed
with psi₀ on the base polynomial ring. Localization extensionality proves these
maps agree everywhere. Apply the quotient evaluation map to the zero expansion.
Split each monomial product into its preceding product and last power. Reindex
the finite sum by Fin.snocEquiv, and collect terms of equal last exponent using
distributivity. The resulting zero sum is the linear combination of root powers
with coefficients equal to the asserted preceding quotient sums. The monic
power basis of AdjoinRoot g, reindexed along its natural-degree equality, is
linearly independent and forces each coefficient to vanish. No hypotheses on
earlier monicity or degrees are used. A zero last degree has no coefficient j. -/
theorem triangularFieldModel_coefficient_descent
    (k : Type u) [Field k] (d n : ℕ) (h : MvPolynomial (Fin d) k)
    (p : (i : Fin (n + 1)) → Polynomial (MvPolynomial (Fin (d + 1 + i.val)) k))
    (e : Fin (n + 1) → ℕ)
    (hp : (p (Fin.last n)).Monic)
    (he : (p (Fin.last n)).natDegree = e (Fin.last n))
    (psi : Localization.Away h →ₐ[k]
      (MvPolynomial (Fin (d + 1 + (n + 1))) k ⧸
        Ideal.ofList (triangularFieldModelEquations k d (n + 1) h p)))
    (hpsi : ∀ r : MvPolynomial (Fin d) k,
      psi (algebraMap _ (Localization.Away h) r) = Ideal.Quotient.mk _
        (MvPolynomial.rename (fun j : Fin d ↦
          (⟨j.val, by omega⟩ : Fin (d + 1 + (n + 1)))) r))
    (psi₀ : Localization.Away h →ₐ[k]
      (MvPolynomial (Fin (d + 1 + n)) k ⧸
        Ideal.ofList (triangularFieldModelEquations k d n h (fun i ↦ p i.castSucc))))
    (hpsi₀ : ∀ r : MvPolynomial (Fin d) k,
      psi₀ (algebraMap _ (Localization.Away h) r) = Ideal.Quotient.mk _
        (MvPolynomial.rename (fun j : Fin d ↦
          (⟨j.val, by omega⟩ : Fin (d + 1 + n))) r))
    (c : (((i : Fin (n + 1)) → Fin (e i)) → Localization.Away h))
    (hc : (∑ a : ((i : Fin (n + 1)) → Fin (e i)),
        psi (c a) * (∏ i : Fin (n + 1),
          (Ideal.Quotient.mk _ (MvPolynomial.X
            (⟨d + 1 + i.val, by omega⟩ : Fin (d + 1 + (n + 1))))) ^ (a i).val)) = 0)
    (j : Fin (e (Fin.last n))) :
    (∑ a : ((i : Fin n) → Fin (e i.castSucc)),
      psi₀ (c (Fin.snoc a j)) * (∏ i : Fin n,
        (Ideal.Quotient.mk _ (MvPolynomial.X
          (⟨d + 1 + i.val, by omega⟩ : Fin (d + 1 + n)))) ^ (a i).val)) = 0 := by
  classical
  let p₀ : (i : Fin n) → Polynomial (MvPolynomial (Fin (d + 1 + i.val)) k) :=
    fun i ↦ p i.castSucc
  let I₀ := Ideal.ofList (triangularFieldModelEquations k d n h p₀)
  let Q₀ := MvPolynomial (Fin (d + 1 + n)) k ⧸ I₀
  by_cases hQ : Subsingleton Q₀
  · let := hQ
    exact Subsingleton.elim _ _
  let : Nontrivial Q₀ := not_subsingleton_iff_nontrivial.mp hQ
  let g : Polynomial Q₀ := (p (Fin.last n)).map (Ideal.Quotient.mk I₀)
  have hg : g.Monic := hp.map _
  have hdeg : g.natDegree = e (Fin.last n) := (hp.natDegree_map _).trans he
  let S := AdjoinRoot g
  let f : Fin (d + 1 + n) → Fin (d + 1 + (n + 1)) := fun t ↦ ⟨t.val, by omega⟩
  let y : Fin (d + 1 + (n + 1)) → S := fun t ↦
    if ht : t.val < d + 1 + n then
      AdjoinRoot.of g (Ideal.Quotient.mk I₀ (MvPolynomial.X ⟨t.val, ht⟩))
    else AdjoinRoot.root g
  let φ : MvPolynomial (Fin (d + 1 + (n + 1))) k →ₐ[k] S := MvPolynomial.aeval y
  have hy (t : Fin (d + 1 + n)) :
      y (f t) = AdjoinRoot.of g (Ideal.Quotient.mk I₀ (MvPolynomial.X t)) := by
    simp [y, f, t.isLt]
  have hy_last : y ⟨d + 1 + n, by omega⟩ = AdjoinRoot.root g := by
    simp [y]
  have hφ : φ.comp (MvPolynomial.rename f) =
      (AdjoinRoot.ofAlgHom k g).comp (Ideal.Quotient.mkₐ k I₀) := by
    ext t
    simp [φ, y, f, t.isLt]
    rfl
  have hφ_apply (q : MvPolynomial (Fin (d + 1 + n)) k) :
      φ (MvPolynomial.rename f q) = AdjoinRoot.of g (Ideal.Quotient.mk I₀ q) :=
    DFunLike.congr_fun hφ q
  let I := Ideal.ofList (triangularFieldModelEquations k d (n + 1) h p)
  have hrel : I ≤ RingHom.ker φ.toRingHom := by
    apply Ideal.span_le.mpr
    intro q hq
    change φ q = 0
    simp only [triangularFieldModelEquations, List.mem_cons, List.mem_ofFn] at hq
    rcases hq with hq | ⟨i, hq⟩
    · subst q
      let q₀ := MvPolynomial.rename (fun t : Fin d ↦
        (⟨t.val, by omega⟩ : Fin (d + 1 + n))) h * MvPolynomial.X ⟨d, by omega⟩ - 1
      have hq₀ : q₀ ∈ I₀ := by
        apply Ideal.subset_span
        simp [q₀, triangularFieldModelEquations]
      have heq : MvPolynomial.rename f q₀ =
          MvPolynomial.rename (fun t : Fin d ↦
            (⟨t.val, by omega⟩ : Fin (d + 1 + (n + 1)))) h *
            MvPolynomial.X ⟨d, by omega⟩ - 1 := by
        simp [q₀, MvPolynomial.rename_rename, f, Function.comp_def]
      rw [← heq, hφ_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hq₀, map_zero]
    · subst q
      by_cases hi : i.val < n
      · let i₀ : Fin n := ⟨i.val, hi⟩
        have hii : i₀.castSucc = i := by ext; rfl
        let q₀ : MvPolynomial (Fin (d + 1 + n)) k :=
          Polynomial.eval₂ (MvPolynomial.rename (fun t : Fin (d + 1 + i₀.val) ↦
            (⟨t.val, by omega⟩ : Fin (d + 1 + n)))).toRingHom
            (MvPolynomial.X ⟨d + 1 + i₀.val, by omega⟩) (p₀ i₀)
        have hq₀ : q₀ ∈ I₀ := by
          apply Ideal.subset_span
          simp only [triangularFieldModelEquations, List.mem_cons, List.mem_ofFn]
          exact Or.inr ⟨i₀, rfl⟩
        have heq : MvPolynomial.rename f q₀ =
            Polynomial.eval₂ (MvPolynomial.rename (fun t : Fin (d + 1 + i.val) ↦
              (⟨t.val, by omega⟩ : Fin (d + 1 + (n + 1))))).toRingHom
              (MvPolynomial.X ⟨d + 1 + i.val, by omega⟩) (p i) := by
          dsimp only [q₀, p₀, i₀, Fin.val_castSucc]
          change (MvPolynomial.rename f).toRingHom
            (Polynomial.eval₂ _ _ (p i)) = _
          rw [Polynomial.hom_eval₂]
          congr 1
          · ext t <;> simp [MvPolynomial.rename_rename, f, Function.comp_def]
          · simp [f]
        rw [← heq, hφ_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hq₀, map_zero]
      · have hii : i = Fin.last n := by ext; simp only [Fin.val_last]; omega
        subst i
        change φ.toRingHom (Polynomial.eval₂ _ _ (p (Fin.last n))) = 0
        rw [Polynomial.hom_eval₂]
        have hhom : φ.toRingHom.comp
            (MvPolynomial.rename (fun t : Fin (d + 1 + n) ↦
              (⟨t.val, by omega⟩ : Fin (d + 1 + (n + 1))))).toRingHom =
            (AdjoinRoot.of g).comp (Ideal.Quotient.mk I₀) :=
          congrArg AlgHom.toRingHom hφ
        have hz := AdjoinRoot.eval₂_root g
        change Polynomial.eval₂ (AdjoinRoot.of g) (AdjoinRoot.root g)
          ((p (Fin.last n)).map (Ideal.Quotient.mk I₀)) = 0 at hz
        rw [Polynomial.eval₂_map] at hz
        convert hz using 1
        congr 1
        change MvPolynomial.aeval y (MvPolynomial.X ⟨d + 1 + n, by omega⟩) = _
        rw [MvPolynomial.aeval_X, hy_last]
  let ev : (MvPolynomial (Fin (d + 1 + (n + 1))) k ⧸ I) →ₐ[k] S :=
    Ideal.Quotient.liftₐ I φ (fun q hq ↦ RingHom.mem_ker.mp (hrel hq))
  have hcoeff : ev.comp psi = (AdjoinRoot.ofAlgHom k g).comp psi₀ := by
    apply AlgHom.toRingHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers h)
    apply RingHom.ext
    intro r
    change ev (psi (algebraMap _ (Localization.Away h) r)) =
      AdjoinRoot.of g (psi₀ (algebraMap _ (Localization.Away h) r))
    rw [hpsi, hpsi₀]
    change φ (MvPolynomial.rename (fun t : Fin d ↦
      (⟨t.val, by omega⟩ : Fin (d + 1 + (n + 1)))) r) = _
    convert hφ_apply (MvPolynomial.rename (fun t : Fin d ↦
      (⟨t.val, by omega⟩ : Fin (d + 1 + n))) r) using 1
    simp [MvPolynomial.rename_rename, f, Function.comp_def]
  have hevc (z : Localization.Away h) :
      ev (psi z) = AdjoinRoot.of g (psi₀ z) := DFunLike.congr_fun hcoeff z
  have hvar (i : Fin n) :
      ev (Ideal.Quotient.mk I (MvPolynomial.X
        (⟨d + 1 + i.castSucc.val, by omega⟩ : Fin (d + 1 + (n + 1))))) =
      AdjoinRoot.of g (Ideal.Quotient.mk I₀ (MvPolynomial.X
        (⟨d + 1 + i.val, by omega⟩ : Fin (d + 1 + n)))) := by
    change MvPolynomial.aeval y (MvPolynomial.X _) = _
    rw [MvPolynomial.aeval_X]
    exact hy ⟨d + 1 + i.val, by omega⟩
  have hvar_last :
      ev (Ideal.Quotient.mk I (MvPolynomial.X
        (⟨d + 1 + (Fin.last n).val, by omega⟩ : Fin (d + 1 + (n + 1))))) =
      AdjoinRoot.root g := by
    change MvPolynomial.aeval y (MvPolynomial.X _) = _
    rw [MvPolynomial.aeval_X]
    exact hy_last
  let B (a : (i : Fin n) → Fin (e i.castSucc)) : Q₀ :=
    ∏ i : Fin n, (Ideal.Quotient.mk I₀ (MvPolynomial.X
      (⟨d + 1 + i.val, by omega⟩ : Fin (d + 1 + n)))) ^ (a i).val
  let C (l : Fin (e (Fin.last n))) : Q₀ :=
    ∑ a : (i : Fin n) → Fin (e i.castSucc), psi₀ (c (Fin.snoc a l)) * B a
  have hprod (a : (i : Fin (n + 1)) → Fin (e i)) :
      ev (∏ i : Fin (n + 1), (Ideal.Quotient.mk I (MvPolynomial.X
        (⟨d + 1 + i.val, by omega⟩ : Fin (d + 1 + (n + 1))))) ^ (a i).val) =
      AdjoinRoot.of g (B (Fin.init a)) * AdjoinRoot.root g ^ (a (Fin.last n)).val := by
    rw [map_prod, Fin.prod_univ_castSucc]
    simp only [map_pow, hvar, hvar_last]
    dsimp only [B]
    rw [map_prod]
    simp only [map_pow, Fin.init]
  have hz := congrArg ev hc
  change ev (∑ a : ((i : Fin (n + 1)) → Fin (e i)),
    psi (c a) * (∏ i : Fin (n + 1), (Ideal.Quotient.mk I (MvPolynomial.X
      (⟨d + 1 + i.val, by omega⟩ : Fin (d + 1 + (n + 1))))) ^ (a i).val)) = ev 0 at hz
  simp only [map_sum, map_mul, hevc, hprod, map_zero] at hz
  have hsum : ∑ l : Fin (e (Fin.last n)), C l • AdjoinRoot.root g ^ l.val = 0 := by
    rw [← (Fin.snocEquiv (fun i ↦ Fin (e i))).sum_comp] at hz
    rw [Fintype.sum_prod_type] at hz
    simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fin.init_snoc, Fin.snoc_last] at hz
    simpa only [C, Algebra.smul_def, AdjoinRoot.algebraMap_eq, map_sum,
      Finset.sum_mul, map_mul, mul_assoc] using hz
  let b := (AdjoinRoot.powerBasis' hg).basis.reindex (finCongr hdeg)
  have hb (l : Fin (e (Fin.last n))) : b l = AdjoinRoot.root g ^ l.val := by
    simp [b, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  have hl : LinearIndependent Q₀ (fun l : Fin (e (Fin.last n)) ↦
      AdjoinRoot.root g ^ l.val) := by
    simpa only [show (b : Fin (e (Fin.last n)) → AdjoinRoot g) =
      (fun l ↦ AdjoinRoot.root g ^ l.val) from funext hb] using b.linearIndependent
  exact Fintype.linearIndependent_iff.mp hl C hsum j

end FieldTheory
