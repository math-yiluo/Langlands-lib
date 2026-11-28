import Langlands.Covering.KazhdanPatterson.BruhatSection
import Langlands.Covering.KazhdanPatterson.CorootCoordinates
import Langlands.Covering.KazhdanPatterson.WeylMatrices

/-! # Diagonal and Weyl coordinates of special linear monomials -/

namespace Langlands.KazhdanPatterson

open Matrix (SpecialLinearGroup)
open Matrix.SpecialLinearGroup (toGL)
open GeneralLinear (monomialRepresentative monomialRepresentative_entry)
open GeneralLinear.Iwasawa (diagonalUnits)

universe u

variable {r : ℕ} {F : Type u} [Field F]

private theorem monomialRepresentative_one (d : Fin (r + 1) → Fˣ) :
    monomialRepresentative 1 d = diagonalUnits d := by
  simp [monomialRepresentative]

private theorem monomialRepresentative_perm_eq {w v : Equiv.Perm (Fin (r + 1))}
    {d e : Fin (r + 1) → Fˣ} (h : monomialRepresentative w d = monomialRepresentative v e) :
    w = v := by
  apply Equiv.ext
  intro j
  have he := congrArg (fun g : GeneralLinear (r + 1) F => g (w j) j) h
  by_contra hne
  have hne' : v j ≠ w j := Ne.symm hne
  simp [monomialRepresentative_entry, hne'] at he

private theorem toGL_diagonal_mul_weyl (t : slDiagonalTorus r F) (w : Equiv.Perm (Fin (r + 1))) :
    ∃ d : Fin (r + 1) → Fˣ, toGL (t.val * weylMatrix w) = monomialRepresentative w d := by
  obtain ⟨a, ha⟩ := t.property
  obtain ⟨e, he⟩ := weylMatrix_monomial (F := F) w
  have ht : toGL t.val = monomialRepresentative 1 a.val := by
    rw [← ha, monomialRepresentative_one]
    exact Units.ext rfl
  refine ⟨(fun j => a.val (w j)) * e, ?_⟩
  rw [map_mul, ht, he, mul_monomialRepresentative, one_mul]

private theorem diagonal_mul_weyl_surjective
    (m : {m : SpecialLinearGroup (Fin (r + 1)) F // IsSpecialLinearMonomial m}) :
    ∃ (t : slDiagonalTorus r F) (w : Equiv.Perm (Fin (r + 1))), t.val * weylMatrix w = m.val := by
  obtain ⟨w, d, hd⟩ := m.property
  obtain ⟨e, he⟩ := weylMatrix_monomial (F := F) w
  let t := m.val * (weylMatrix w)⁻¹
  let a (i : Fin (r + 1)) := d (w⁻¹ i) * (e (w⁻¹ i))⁻¹
  have ht : toGL t = diagonalUnits a := by
    apply mul_right_cancel (b := toGL (weylMatrix w))
    calc
      toGL t * toGL (weylMatrix w) = toGL m.val := by
        simp only [← map_mul, t, inv_mul_cancel_right]
      _ = diagonalUnits a * toGL (weylMatrix w) := by
        rw [hd, he, ← monomialRepresentative_one, mul_monomialRepresentative, one_mul]
        congr 1
        funext j
        simp [a]
  have hdiag : t.val.IsDiag := by
    have ha : t.val = Matrix.diagonal (fun i => (a i : F)) := congrArg Units.val ht
    rw [ha]
    exact Matrix.isDiag_diagonal _
  exact ⟨⟨t, (mem_slDiagonalTorus r F t).mpr hdiag⟩, w, inv_mul_cancel_right _ _⟩

/-- Every special linear monomial matrix is uniquely a determinant-one diagonal times the chosen
representative of its permutation. -/
noncomputable def slMonomialWeylEquiv :
    (slDiagonalTorus r F × Equiv.Perm (Fin (r + 1))) ≃
      {m : SpecialLinearGroup (Fin (r + 1)) F // IsSpecialLinearMonomial m} :=
  Equiv.ofBijective (fun p => ⟨p.1.val * weylMatrix p.2, ⟨p.2, toGL_diagonal_mul_weyl p.1 p.2⟩⟩)
    ⟨by
      intro p q h
      obtain ⟨d, hd⟩ := toGL_diagonal_mul_weyl p.1 p.2
      obtain ⟨e, he⟩ := toGL_diagonal_mul_weyl q.1 q.2
      have hm : p.1.val * weylMatrix p.2 = q.1.val * weylMatrix q.2 := congrArg Subtype.val h
      have hw : p.2 = q.2 :=
        monomialRepresentative_perm_eq (hd.symm.trans ((congrArg toGL hm).trans he))
      rw [hw] at hm
      exact Prod.ext (Subtype.ext (mul_right_cancel hm)) hw,
    by
      intro m
      obtain ⟨t, w, h⟩ := diagonal_mul_weyl_surjective m
      exact ⟨(t, w), Subtype.ext h⟩⟩

@[simp]
theorem slMonomialWeylEquiv_apply_val (t : slDiagonalTorus r F) (w : Equiv.Perm (Fin (r + 1))) :
    (slMonomialWeylEquiv (t, w)).val = t.val * weylMatrix w := rfl

@[simp]
theorem slMonomialWeylEquiv_symm_one :
    (slMonomialWeylEquiv (F := F) (r := r)).symm ⟨1, isSpecialLinearMonomial_one⟩ = (1, 1) := by
  apply slMonomialWeylEquiv.injective
  rw [Equiv.apply_symm_apply]
  exact Subtype.ext (by simp)

end Langlands.KazhdanPatterson
