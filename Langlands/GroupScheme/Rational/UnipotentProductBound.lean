import Langlands.GroupScheme.Absolute.UnipotentPointsSolvable

/-! # Uniform products of differences in unipotent representations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}
    {m : ℕ}

/-- A uniform bound for products of matrix differences, on every scheme test. -/
def HasUnipotentProductBound (ρ : MatrixRepresentation G (Fin m)) (d : ℕ) : Prop :=
  ∀ (T : Over (Spec R)) (l : List (T ⟶ G.X)), d ≤ l.length →
    (l.map (fun x => (ρ.pointMatrix T x).val - 1)).prod = 0

section MatrixProducts

variable {S : Type*} [CommRing S]

private theorem tail_list_prod (l : List (Matrix (Fin (m + 1)) (Fin (m + 1)) S))
    (hl : ∀ M ∈ l, ∀ i : Fin m, M i.succ 0 = 0) :
    tail l.prod = (l.map tail).prod := by
  induction l with
  | nil => exact tail_one
  | cons M l ih =>
    rw [List.prod_cons, tail_mul _ _ (hl M (by simp)), List.map_cons,
      List.prod_cons, ih (fun N hN => hl N (by simp [hN]))]

private theorem list_prod_lower_first_column
    (l : List (Matrix (Fin (m + 1)) (Fin (m + 1)) S))
    (hl : ∀ M ∈ l, ∀ i : Fin m, M i.succ 0 = 0) :
    ∀ i : Fin m, l.prod i.succ 0 = 0 := by
  induction l with
  | nil =>
    intro i
    simp
  | cons M l ih =>
    intro i
    have hM := hl M (by simp) i
    have hrest := ih (fun N hN => hl N (by simp [hN]))
    simp [List.prod_cons, Matrix.mul_apply, Fin.sum_univ_succ, hM, hrest]

private theorem mul_eq_zero_of_first_column_tail
    (M N : Matrix (Fin (m + 1)) (Fin (m + 1)) S)
    (hM : ∀ i, M i 0 = 0)
    (hN : ∀ i : Fin m, N i.succ 0 = 0) (htail : tail N = 0) :
    M * N = 0 := by
  have hbottom : ∀ (i : Fin m) (j : Fin (m + 1)), N i.succ j = 0 := by
    intro i j
    refine Fin.cases (hN i) (fun j => ?_) j
    exact congrArg (fun P : Matrix (Fin m) (Fin m) S => P i j) htail
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_succ, hM, hbottom]

private theorem list_prod_units_conjugate {A : Type*} [Ring A]
    (g : Aˣ) (l : List A) :
    (l.map (fun M => (g : A) * M * ↑g⁻¹)).prod =
      (g : A) * l.prod * ↑g⁻¹ := by
  induction l with
  | nil => simp
  | cons M l ih =>
    simp only [List.map_cons, List.prod_cons, ih]
    simp only [mul_assoc, Units.inv_mul_cancel_left]

end MatrixProducts

/-- Products of matrix differences vanish once their length reaches the
representation dimension. The same bound works for every test scheme. -/
theorem hasUnipotentProductBound_of_isUnipotent {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsUnipotent G) (m : ℕ) :
    ∀ ρ : MatrixRepresentation G (Fin m), ρ.HasUnipotentProductBound m := by
  induction m with
  | zero =>
    intro ρ T l _hl
    ext i j
    exact Fin.elim0 i
  | succ m ih =>
    intro ρ T l hl
    obtain ⟨v, hv0, hv⟩ := hG (Fin (m + 1)) ρ
    obtain ⟨g, hg⟩ := exists_mulVec_eq_firstBasisVector hv0
    let ρ' := ρ.conjugate (basePoint g)
    have hfix : ρ'.IsFixedVector (firstBasisVector k m) :=
      hg ▸ isFixedVector_conjugate hv g
    have htail := ih (tailRepresentation ρ' hfix)
    let A : (T ⟶ G.X) → Matrix (Fin (m + 1)) (Fin (m + 1)) Γ(T.left, ⊤) :=
      fun x => (ρ'.pointMatrix T x).val - 1
    have hcol : ∀ x i, A x i 0 = 0 := by
      intro x i
      have h := mem_fixesFirstSubgroup_apply
        (pointMatrix_mem_fixesFirstSubgroup ρ' hfix T x) i
      simp only [A, Matrix.sub_apply, h, firstBasisVector, Pi.single_apply,
        Matrix.one_apply]
      split_ifs <;> simp_all
    have hzero : (l.map A).prod = 0 := by
      cases l with
      | nil => simp at hl
      | cons x l =>
        have hlen : m ≤ l.length := Nat.le_of_succ_le_succ hl
        have ht := htail T l hlen
        have htailA : ∀ y, tail (A y) =
            ((tailRepresentation ρ' hfix).pointMatrix T y).val - 1 := by
          intro y
          rw [tailRepresentation_pointMatrix]
          ext i j
          simp [A, tail, tailPointMatrix, fixingPointMatrix, Matrix.one_apply,
            Fin.succ_inj]
        have htprod : tail (l.map A).prod = 0 := by
          rw [tail_list_prod _ (by
            intro M hM i
            obtain ⟨y, _hy, rfl⟩ := List.mem_map.1 hM
            exact hcol y i.succ)]
          simpa only [List.map_map, Function.comp_def, htailA] using ht
        rw [List.map_cons, List.prod_cons]
        apply mul_eq_zero_of_first_column_tail _ _ (hcol x) _ htprod
        apply list_prod_lower_first_column
        intro M hM i
        obtain ⟨y, _hy, rfl⟩ := List.mem_map.1 hM
        exact hcol y i.succ
    let C := Matrix.GeneralLinearGroup.map (scalarMap T) g
    have hA : ∀ x, A x = C.val * ((ρ.pointMatrix T x).val - 1) * (C⁻¹).val := by
      intro x
      change ((ρ.conjugate (basePoint g)).pointMatrix T x).val - 1 = _
      rw [conjugate_pointMatrix, pointsEquiv_constantPoint_basePoint]
      simp only [Units.val_mul, mul_sub, sub_mul, mul_one,
        Units.mul_inv]
      rfl
    have heq : (l.map A).prod =
        C.val * (l.map (fun x => (ρ.pointMatrix T x).val - 1)).prod * (C⁻¹).val := by
      calc
        (l.map A).prod =
            ((l.map (fun x => (ρ.pointMatrix T x).val - 1)).map
              (fun M => C.val * M * (C⁻¹).val)).prod := by
          simp only [List.map_map, Function.comp_def]
          congr 1
          exact List.map_congr_left (fun x _hx => hA x)
        _ = _ := list_prod_units_conjugate C _
    rw [heq] at hzero
    have hc := congrArg (fun M => (C⁻¹).val * M * C.val) hzero
    simpa [mul_assoc] using hc

/-- In particular each represented point is a unipotent matrix, uniformly
including on nonreduced test schemes. -/
theorem pointMatrix_sub_one_pow_eq_zero_of_isUnipotent {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsUnipotent G)
    (ρ : MatrixRepresentation G (Fin m)) (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ G.X) :
    ((ρ.pointMatrix T x).val - 1) ^ m = 0 := by
  simpa using hasUnipotentProductBound_of_isUnipotent hG m ρ T (List.replicate m x)
    (by simp)

end Langlands.GroupScheme.MatrixRepresentation
