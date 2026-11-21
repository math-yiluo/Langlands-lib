import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.CliffordAlgebra.Inversion
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

/-! # The scalar centralizer in the even Clifford algebra -/

noncomputable section

universe u v w

namespace Langlands.QuadraticForm

open QuadraticMap CliffordAlgebra

variable {R : Type u} {V : Type v} {I : Type w}
  [CommRing R] [Invertible (2 : R)] [AddCommGroup V] [Module R V] [LinearOrder I]
  (Q : QuadraticForm R V) (b : Module.Basis I R V)

omit [Invertible (2 : R)] in
private theorem contractLeft_prod_of_vanishes (Q' : QuadraticForm R V)
    (d : Module.Dual R V) (l : List V) (h : ∀ x ∈ l, d x = 0) :
    contractLeft (Q := Q') d (l.map (ι Q')).prod = 0 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, contractLeft_ι_mul, h x (List.mem_cons_self ..),
      zero_smul, ih (fun y hy => h y (List.mem_cons_of_mem _ hy)), mul_zero, sub_zero]

omit [LinearOrder I] in
private theorem equivExterior_prod_of_orthogonal
    (h : ∀ i j, i ≠ j → polar Q (b i) (b j) = 0) (l : List I) (hl : l.Nodup) :
    equivExterior Q (l.map (fun i => ι Q (b i))).prod =
      (l.map (fun i => ExteriorAlgebra.ι R (b i))).prod := by
  induction l with
  | nil => exact changeForm_one (changeForm.associated_neg_proof (Q := Q))
  | cons i l ih =>
    have h' := List.nodup_cons.mp hl
    simp only [List.map_cons, List.prod_cons]
    change changeForm changeForm.associated_neg_proof (ι Q (b i) * _) = _
    rw [changeForm_ι_mul]
    change ExteriorAlgebra.ι R (b i) * equivExterior Q _ -
      contractLeft (Q := 0) ((associated (-Q)) (b i)) (equivExterior Q _) = _
    rw [ih h'.2]
    have hc : contractLeft (Q := 0) ((associated (-Q)) (b i))
        (l.map (fun j => ExteriorAlgebra.ι R (b j))).prod = 0 := by
      rw [show l.map (fun j => ExteriorAlgebra.ι R (b j)) = (l.map b).map (ι 0) by
        simp [List.map_map, Function.comp_def, ExteriorAlgebra.ι]]
      apply contractLeft_prod_of_vanishes
      intro v hv
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv
      change associatedHom R (-Q) (b i) (b j) = _
      rw [associated_apply]
      change ⅟(2 : Module.End R R) • polar (-(Q : V → R)) (b i) (b j) = 0
      rw [polar_neg, h i j (fun he => h'.1 (he ▸ hj)), neg_zero, smul_zero]
    rw [hc, sub_zero]

/-- The Clifford basis indexed by subsets of an orthogonal basis of the quadratic space. -/
def cliffordOrthogonalBasis : Module.Basis (Finset I) R (CliffordAlgebra Q) :=
  b.ExteriorAlgebra.map (equivExterior Q).symm

/-- Its basis vector is the ordered product of the corresponding Clifford vectors. -/
theorem cliffordOrthogonalBasis_apply
    (h : ∀ i j, i ≠ j → polar Q (b i) (b j) = 0) (s : Finset I) :
    cliffordOrthogonalBasis Q b s = (s.sort.map (fun i => ι Q (b i))).prod := by
  apply (equivExterior Q).injective
  rw [equivExterior_prod_of_orthogonal Q b h _ (Finset.sort_nodup s (· ≤ ·))]
  change equivExterior Q ((equivExterior Q).symm (b.ExteriorAlgebra s)) = _
  rw [LinearEquiv.apply_symm_apply, ExteriorAlgebra.basis_apply]
  change ExteriorAlgebra.ιMulti R s.card (b ∘ s.orderEmbOfFin rfl) = _
  simp only [ExteriorAlgebra.ιMulti_apply, List.ofFn_eq_map, Function.comp_apply]
  rw [show ((List.finRange s.card).map (fun i => ExteriorAlgebra.ι R
      (b (s.orderEmbOfFin rfl i)))) = s.sort.map (fun j => ExteriorAlgebra.ι R (b j)) by
    rw [← Finset.listMap_orderEmbOfFin_finRange s rfl, List.map_map]
    simp [Function.comp_def]]

private def twistedConjugation (u : (CliffordAlgebra Q)ˣ) :
    CliffordAlgebra Q →ₐ[R] CliffordAlgebra Q where
  toFun x := (u : CliffordAlgebra Q) * involute x * ↑u⁻¹
  map_one' := by rw [map_one, mul_one, Units.mul_inv]
  map_zero' := by rw [map_zero, mul_zero, zero_mul]
  map_add' x y := by rw [map_add, mul_add, add_mul]
  map_mul' x y := by
    rw [map_mul]
    calc
      _ = ((u : CliffordAlgebra Q) * involute x) * (involute y * ↑u⁻¹) := by
        simp only [mul_assoc]
      _ = _ := by simp only [mul_assoc, ← mul_assoc (↑u⁻¹ : CliffordAlgebra Q),
        Units.inv_mul, one_mul]
  commutes' r := by rw [AlgHom.commutes, ← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]

omit [Invertible (2 : R)] in
private theorem twistedConjugation_orthogonal_vector
    (h : ∀ i j, i ≠ j → polar Q (b i) (b j) = 0)
    (i j : I) (u : (CliffordAlgebra Q)ˣ) (hu : ↑u = ι Q (b i)) :
    twistedConjugation Q u (ι Q (b j)) = (if i = j then -1 else (1 : R)) • ι Q (b j) := by
  classical
  change ↑u * involute (ι Q (b j)) * ↑u⁻¹ = _
  by_cases hi : i = j
  · subst j
    rw [ite_eq_left rfl, involute_ι, ← hu, mul_neg, neg_mul, mul_assoc, Units.mul_inv, mul_one,
      neg_one_smul]
  · rw [ite_eq_right hi, one_smul, involute_ι, mul_neg, neg_mul]
    have hc : ι Q (b i) * ι Q (b j) = -(ι Q (b j) * ι Q (b i)) := by
      rw [ι_mul_ι_comm, h i j hi, map_zero, zero_sub]
    rw [hu, hc, ← hu, neg_mul, neg_neg, mul_assoc, Units.mul_inv, mul_one]

omit [Invertible (2 : R)] in
private theorem twistedConjugation_prod
    (h : ∀ i j, i ≠ j → polar Q (b i) (b j) = 0)
    (i : I) (u : (CliffordAlgebra Q)ˣ) (hu : ↑u = ι Q (b i)) (l : List I) :
    twistedConjugation Q u (l.map (fun j => ι Q (b j))).prod =
      ((-1 : R) ^ l.count i) • (l.map (fun j => ι Q (b j))).prod := by
  classical
  induction l with
  | nil => simp
  | cons j l ih =>
    rw [List.map_cons, List.prod_cons, map_mul, twistedConjugation_orthogonal_vector Q b h i j u hu,
      ih, smul_mul_smul_comm]
    by_cases hi : i = j
    · subst j
      simp [pow_succ, mul_comm]
    · simp [hi, Ne.symm hi]

/-- An element fixed by the grade involution and commuting with all vectors is a scalar when
there is an orthogonal basis of vectors with unit values. -/
theorem exists_scalar_of_involute_eq_of_commutes_vectors
    (h : ∀ i j, i ≠ j → polar Q (b i) (b j) = 0) (hb : ∀ i, IsUnit (Q (b i)))
    {x : CliffordAlgebra Q} (he : involute x = x) (hx : ∀ v, Commute (ι Q v) x) :
    ∃ r : R, algebraMap R (CliffordAlgebra Q) r = x := by
  classical
  let B := cliffordOrthogonalBasis Q b
  have hs (s : Finset I) (hs₀ : s ≠ ∅) : B.repr x s = 0 := by
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs₀
    let u := (isUnit_ι_of_isUnit Q (hb i)).unit
    have hu : (u : CliffordAlgebra Q) = ι Q (b i) := IsUnit.unit_spec _
    let f := twistedConjugation Q u
    have hfx : f x = x := by
      change (u : CliffordAlgebra Q) * involute x * ↑u⁻¹ = x
      rw [he, hu, (hx (b i)).eq, ← hu, mul_assoc, Units.mul_inv, mul_one]
    have hcoord : (B.coord s).comp f.toLinearMap = -(B.coord s) := by
      apply B.ext
      intro t
      change B.coord s (f (B t)) = -(B.coord s (B t))
      have hft : f (B t) = ((-1 : R) ^ t.sort.count i) • B t := by
        simp only [B, cliffordOrthogonalBasis_apply Q b h]
        exact twistedConjugation_prod Q b h i u hu t.sort
      rw [hft, map_smul]
      by_cases ht : t = s
      · subst t
        have hn : s.sort.count i = 1 := List.count_eq_one_of_mem
          (Finset.sort_nodup s (· ≤ ·)) ((Finset.mem_sort (· ≤ ·)).mpr hi)
        simp [hn]
      · simp [Module.Basis.coord_apply, Ne.symm ht]
    have hh := DFunLike.congr_fun hcoord x
    change B.coord s (f x) = -(B.coord s x) at hh
    rw [hfx] at hh
    change B.repr x s = -(B.repr x s) at hh
    apply (isUnit_of_invertible (2 : R)).mul_left_cancel
    rw [mul_zero, two_mul]
    exact (congrArg (· + B.repr x s) hh).trans (neg_add_cancel _)
  refine ⟨B.repr x ∅, B.repr.injective ?_⟩
  have hB : B ∅ = 1 := by simp [B, cliffordOrthogonalBasis_apply Q b h]
  rw [Algebra.algebraMap_eq_smul_one, ← hB, map_smul]
  ext s
  by_cases hse : s = ∅
  · subst s
    simp
  · simp [hs s hse, hse]

end Langlands.QuadraticForm
