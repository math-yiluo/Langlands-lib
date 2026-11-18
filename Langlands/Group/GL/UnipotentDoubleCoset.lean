import Langlands.Group.GL.UpperBruhatCoordinatesProof
import Langlands.Group.GL.UpperBruhatFiltrationGeometryProof
import Mathlib.GroupTheory.DoubleCoset

/-! # Monomial representatives of upper-unipotent double cosets -/

noncomputable section

namespace Langlands.GeneralLinear

open UpperBruhatCoordinates

variable {K : Type*} [Field K] {n : ℕ}

/-- The monomial matrix with column `j` supported at row `w j` and value `d j`. -/
def monomialRepresentative (w : Equiv.Perm (Fin n)) (d : Fin n → Kˣ) : GeneralLinear n K :=
  permutation n K w * Iwasawa.diagonalUnits d

/-- Its entry records the permutation support and the diagonal scalar. -/
theorem monomialRepresentative_entry (w : Equiv.Perm (Fin n)) (d : Fin n → Kˣ) (i j : Fin n) :
    monomialRepresentative w d i j = if w j = i then (d j : K) else 0 := by
  rw [monomialRepresentative, permutation_mul_entry]
  change (Matrix.diagonal fun a => (d a : K)) (w⁻¹ i) j = _
  rw [Matrix.diagonal_apply]
  by_cases hij : w j = i
  · subst i
    simp
  · have h : w.symm i ≠ j := by
      intro he
      apply hij
      simpa using (congrArg w he).symm
    simp [hij, h]

/-- Every invertible matrix factors as a monomial matrix between two upper-unipotents. -/
theorem exists_unipotent_mul_monomial_mul (g : GeneralLinear n K) :
    ∃ (w : Equiv.Perm (Fin n)) (d : Fin n → Kˣ) (u v : upperUnipotent n K),
      g = u.val * monomialRepresentative w d * v.val := by
  obtain ⟨w, hw⟩ := exists_mem_upperBruhatCell g
  obtain ⟨⟨b, v⟩, hb⟩ := (cellEquiv w).surjective ⟨g, hw⟩
  obtain ⟨⟨u, d⟩, hu⟩ := (torusSplitEquiv w).surjective b
  refine ⟨w, d, u, ⟨v.val, v.property.1⟩, ?_⟩
  have h := congrArg Subtype.val hb
  rw [cellEquiv_apply, upperBruhatCellMap_val] at h
  change b.val * permutation n K w * v.val = g at h
  have hu' := congrArg Subtype.val hu
  change u.val * Iwasawa.diagonalUnits (fun i => d (w⁻¹ i)) = b.val at hu'
  rw [← h, ← hu', mul_assoc u.val, ← permutation_mul_diagonalUnits]
  rfl

private theorem monomial_diagonal_eq_of_mul_unipotent (w : Equiv.Perm (Fin n))
    (d d' : Fin n → Kˣ) (u v : upperUnipotent n K)
    (h : monomialRepresentative w d' = u.val * monomialRepresentative w d * v.val) : d = d' := by
  let p := permutation n K w
  let D := Iwasawa.diagonalUnits (F := K) (m := n)
  change p * D d' = u.val * (p * D d) * v.val at h
  have hc : p⁻¹ * u.val * p = D d' * v.val⁻¹ * (D d)⁻¹ := by
    calc
      _ = p⁻¹ * (u.val * (p * D d) * v.val) * v.val⁻¹ * (D d)⁻¹ := by group
      _ = _ := by rw [← h]; group
  funext i
  have he := congrArg (fun g : GeneralLinear n K => g i i) hc
  change ((permutation n K w)⁻¹ * u.val * permutation n K w) i i =
    (Iwasawa.diagonalUnits d' * v.val⁻¹ * (Iwasawa.diagonalUnits d)⁻¹) i i at he
  rw [permutation_inv, mul_permutation_entry, permutation_mul_entry, inv_inv] at he
  rw [← map_inv, Iwasawa.diagonalUnits_mul_mul_apply, Pi.inv_apply,
    Units.val_inv_eq_inv_val] at he
  have hv : (v.val⁻¹ : GeneralLinear n K) i i = 1 := (v⁻¹).property.2 i
  rw [u.property.2, hv, mul_one] at he
  exact Units.ext ((mul_inv_eq_one₀ (Units.ne_zero (d i))).mp he.symm).symm

/-- Bruhat permutation and diagonal units give unique upper-unipotent double-coset coordinates. -/
theorem monomialDoubleCoset_bijective : Function.Bijective
    (fun p : Equiv.Perm (Fin n) × (Fin n → Kˣ) =>
      DoubleCoset.mk (upperUnipotent n K) (upperUnipotent n K)
        (monomialRepresentative p.1 p.2)) := by
  constructor
  · rintro ⟨w, d⟩ ⟨w', d'⟩ he
    obtain ⟨u, hu, v, hv, h⟩ := DoubleCoset.eq.mp he
    have h₁ := unipotent_diagonal_mem_upperBruhatCell n w ⟨u, hu⟩ ⟨v, hv⟩ d
    have h₂ := unipotent_diagonal_mem_upperBruhatCell n w' (1 : upperUnipotent n K) 1 d'
    have h₁' : monomialRepresentative w' d' ∈ upperBruhatCell n K w := by
      rw [h, monomialRepresentative, ← mul_assoc u]
      exact h₁
    have h₂' : monomialRepresentative w' d' ∈ upperBruhatCell n K w' := by
      simpa only [monomialRepresentative, Subgroup.coe_one, one_mul, mul_one] using h₂
    have hww' := upperBruhatCell_index_eq h₁' h₂'
    subst w'
    exact Prod.ext rfl (monomial_diagonal_eq_of_mul_unipotent w d d' ⟨u, hu⟩ ⟨v, hv⟩ h)
  · intro q
    obtain ⟨g, rfl⟩ := Quotient.exists_rep q
    obtain ⟨w, d, u, v, he⟩ := exists_unipotent_mul_monomial_mul g
    exact ⟨(w, d), DoubleCoset.eq.mpr ⟨u.val, u.property, v.val, v.property, he⟩⟩

/-- The double cosets of the upper-unipotent subgroup are indexed by a permutation and a unit
in each column. -/
def monomialDoubleCosetEquiv :
    (Equiv.Perm (Fin n) × (Fin n → Kˣ)) ≃
      DoubleCoset.Quotient (upperUnipotent n K : Set (GeneralLinear n K)) (upperUnipotent n K) :=
  Equiv.ofBijective _ monomialDoubleCoset_bijective

end Langlands.GeneralLinear
