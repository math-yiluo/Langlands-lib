import Langlands.TraceFormula.UnitDiscriminantCosetStatement
import Langlands.BaseChange.RegularCyclicBasis
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Proof of the centralizer coset property at unit discriminant

`unitDiscriminantCentralizerCoset` proves `UnitDiscriminantCentralizerCosetStatement`.
Let `O` be a valuation subring of `F`, let `γ ∈ GL_n(O)` have a characteristic polynomial
whose discriminant is a unit of `O`, and let `x ∈ GL_n(F)` with `δ = x⁻¹ * γ * x ∈ GL_n(O)`.

* `separable_charpoly_of_valuation_discr_eq_one`: the characteristic polynomial `p` of `γ`
  over `O` is separable over `O`. For `deg p > 0`, `Polynomial.resultant_deriv` identifies the
  resultant of `p` and `p'` in sizes `deg p`, `deg p - 1` with `± disc p`, so it is a unit, and
  `Polynomial.exists_mul_add_mul_eq_C_resultant` gives a Bézout identity `a p + b p' = 1`.
* `exists_units_conj_of_charpoly_separable`: over a local ring, two matrices with the same
  separable characteristic polynomial are conjugate by an invertible matrix over the ring.
  A cyclic vector of the reduced matrix (`Langlands.BaseChange.regularCyclicBasis`) lifts to
  a vector whose cyclic-basis matrix has unit determinant, and
  `Langlands.BaseChange.cyclicBasis_conjugator` compares the two cyclic bases.
* With `z ∈ GL_n(O)` such that `z⁻¹ * γ * z = δ`, the element `c = x * z⁻¹` commutes with `γ`
  and `x = c * z`.

The discrete valuation hypothesis of the statement is not used: the argument needs only that
the valuation subring `O` is a local ring.
-/

noncomputable section

open Matrix Polynomial Langlands.BaseChange

namespace Langlands.TraceFormula

universe u

section LocalRing

variable {R : Type*} [CommRing R] {n : ℕ}

/-- A monic polynomial of positive degree is separable when its resultant with its derivative,
taken in the sizes `deg p` and `deg p - 1`, is a unit. -/
theorem separable_of_isUnit_resultant_derivative {p : R[X]} (hdeg : 0 < p.natDegree)
    (h : IsUnit (p.resultant (derivative p) p.natDegree (p.natDegree - 1))) : p.Separable := by
  obtain ⟨a, b, -, -, e⟩ := exists_mul_add_mul_eq_C_resultant p (derivative p) le_rfl
    (natDegree_derivative_le p) (Or.inl hdeg.ne')
  refine ⟨C (↑h.unit⁻¹ : R) * a, C (↑h.unit⁻¹ : R) * b, ?_⟩
  calc C (↑h.unit⁻¹ : R) * a * p + C (↑h.unit⁻¹ : R) * b * derivative p
        = C (↑h.unit⁻¹ : R) * (p * a + derivative p * b) := by ring
    _ = 1 := by rw [e, ← C_mul, h.val_inv_mul, C_1]

/-- Over a local ring, a matrix whose reduced characteristic polynomial is separable has an
invertible cyclic basis: lift a cyclic vector of the reduced matrix. -/
theorem exists_isUnit_cyclicBasisMatrix_of_residue [IsLocalRing R]
    (A : Matrix (Fin n) (Fin n) R)
    (hsep : (A.map (IsLocalRing.residue R)).charpoly.Separable) :
    ∃ v, IsUnit (cyclicBasisMatrix A v) := by
  let f := IsLocalRing.residue R
  obtain ⟨v₀, hv₀⟩ := regularCyclicBasis (IsLocalRing.ResidueField R) n (A.map f) hsep
  choose v hv using fun i => IsLocalRing.residue_surjective (v₀ i)
  have he : f ∘ v = v₀ := funext hv
  have hM : (cyclicBasisMatrix A v).map f = cyclicBasisMatrix (A.map f) v₀ := by
    rw [cyclicBasisMatrix_map, he]
  refine ⟨v, (Matrix.isUnit_iff_isUnit_det _).mpr ?_⟩
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  change f (cyclicBasisMatrix A v).det ≠ 0
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hM]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hv₀).ne_zero

/-- Over a local ring, two matrices with the same characteristic polynomial are conjugate by an
invertible matrix over the ring when that polynomial is separable. -/
theorem exists_units_conj_of_charpoly_separable [IsLocalRing R]
    {A B : Matrix (Fin n) (Fin n) R} (hp : A.charpoly = B.charpoly)
    (hs : A.charpoly.Separable) :
    ∃ z : GL (Fin n) R, A * z = z * B := by
  have hsepA : (A.map (IsLocalRing.residue R)).charpoly.Separable := by
    rw [Matrix.charpoly_map]
    exact hs.map
  have hsepB : (B.map (IsLocalRing.residue R)).charpoly.Separable := by
    rw [Matrix.charpoly_map, ← hp]
    exact hs.map
  obtain ⟨a, ha⟩ := exists_isUnit_cyclicBasisMatrix_of_residue A hsepA
  obtain ⟨b, hb⟩ := exists_isUnit_cyclicBasisMatrix_of_residue B hsepB
  exact ⟨ha.unit * hb.unit⁻¹, cyclicBasis_conjugator ha hb hp⟩

end LocalRing

section ValuationSubring

variable {F : Type u} [Field F] (O : ValuationSubring F) {n : ℕ}

/-- If the characteristic polynomial of a matrix over the valuation subring `O` has, over `F`,
a discriminant of valuation `1`, then that characteristic polynomial is separable over `O`. -/
theorem separable_charpoly_of_valuation_discr_eq_one (A : Matrix (Fin n) (Fin n) O)
    (h : O.valuation (A.map O.subtype).charpoly.discr = 1) : A.charpoly.Separable := by
  have hmonic : A.charpoly.Monic := charpoly_monic A
  rcases Nat.eq_zero_or_pos A.charpoly.natDegree with h0 | hpos
  · rw [eq_one_of_monic_natDegree_zero hmonic h0]
    exact separable_one
  · apply separable_of_isUnit_resultant_derivative hpos
    rw [ValuationSubring.valuation_eq_one_iff]
    have hdeg : (A.charpoly.map O.subtype).natDegree = A.charpoly.natDegree :=
      hmonic.natDegree_map _
    have key := resultant_deriv (f := A.charpoly.map O.subtype)
      (natDegree_pos_iff_degree_pos.mp (hdeg ▸ hpos))
    rw [hdeg, derivative_map, resultant_map_map, (hmonic.map _).leadingCoeff, mul_one,
      ← Matrix.charpoly_map] at key
    change O.valuation (O.subtype _) = 1
    rw [key, Valuation.map_mul, h, mul_one, Valuation.map_pow, Valuation.map_neg,
      Valuation.map_one, one_pow]

end ValuationSubring

open Langlands.GeneralLinearGroup in
/-- Proof of `UnitDiscriminantCentralizerCosetStatement`: integral conjugacy of `γ` and
`x⁻¹ * γ * x` over `O` gives the coset decomposition. -/
theorem unitDiscriminantCentralizerCoset : UnitDiscriminantCentralizerCosetStatement.{u} := by
  intro F _ O _ n γ hγ hdisc x hx
  let ι := O.subtype
  have hγ' := (mem_integralSubgroup (Fin n) O.toSubring γ).mp hγ
  have hx' := (mem_integralSubgroup (Fin n) O.toSubring (x⁻¹ * γ * x)).mp hx
  let A : Matrix (Fin n) (Fin n) O :=
    Matrix.of fun i j => ⟨(γ : Matrix (Fin n) (Fin n) F) i j, hγ'.1 i j⟩
  let B : Matrix (Fin n) (Fin n) O :=
    Matrix.of fun i j => ⟨((x⁻¹ * γ * x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j, hx'.1 i j⟩
  have hA : A.map ι = γ := rfl
  have hB : B.map ι = ((x⁻¹ * γ * x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := rfl
  have hAB : A.charpoly = B.charpoly := by
    apply Polynomial.map_injective ι Subtype.val_injective
    rw [← Matrix.charpoly_map, ← Matrix.charpoly_map, hA, hB]
    simpa only [Units.val_mul, Matrix.coe_units_inv] using
      (Matrix.charpoly_units_conj' x (γ : Matrix (Fin n) (Fin n) F)).symm
  have hs : A.charpoly.Separable :=
    separable_charpoly_of_valuation_discr_eq_one O A (by rw [hA]; exact hdisc)
  obtain ⟨z₀, hz₀⟩ := exists_units_conj_of_charpoly_separable hAB hs
  let z := Matrix.GeneralLinearGroup.map ι z₀
  have hz : z ∈ integralSubgroup (Fin n) O.toSubring := by
    rw [mem_integralSubgroup]
    exact ⟨fun i j => (z₀ i j).property, fun i j => (z₀⁻¹ i j).property⟩
  have hcomm : γ * z = z * (x⁻¹ * γ * x) := by
    apply Units.ext
    change (γ : Matrix (Fin n) (Fin n) F) * z₀.val.map ι =
      z₀.val.map ι * ((x⁻¹ * γ * x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
    have h := congrArg ι.mapMatrix hz₀
    simpa only [map_mul, RingHom.mapMatrix_apply, hA, hB] using h
  have hconj : x⁻¹ * γ * x = z⁻¹ * γ * z := by
    rw [mul_assoc z⁻¹, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
  refine ⟨x * z⁻¹, ?_, z, hz, by group⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro g rfl
  calc g * (x * z⁻¹) = x * (x⁻¹ * g * x) * z⁻¹ := by group
    _ = x * (z⁻¹ * g * z) * z⁻¹ := by rw [hconj]
    _ = x * z⁻¹ * g := by group

end Langlands.TraceFormula
