import Langlands.Representation.AffineGeneric.Determinant
import Langlands.JacquetLanglands.RegularElliptic
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic

/-!
# Elements of `I⁺` with nonzero invariant `D` are regular elliptic

Let `F` be a nonarchimedean local field of characteristic zero with uniformizer `ϖ`. If
`γ ∈ I⁺` and `D(γ) = ∏ᵢ aᵢ(γ - 1)` is nonzero, then `γ` is regular elliptic. Indeed
`Y = γ - 1` lies in the radical `𝔓`, so its characteristic polynomial has integral
coefficients and reduces to `X^{m+1}` modulo `𝔭` (the reduction of `Y` is strictly upper
triangular). By the determinant identity `D(γ) = res((-1)^m ϖ⁻¹ det Y)`, the determinant of
`Y` has the valuation of `ϖ`, so the constant term does not lie in `𝔭²`. Hence the
characteristic polynomial of `Y` is an Eisenstein polynomial, so it is irreducible over `F`;
the characteristic polynomial of `γ = Y + 1` is its translate by `-1`, so it is irreducible
too, and separable because `F` is perfect.
-/

noncomputable section

namespace Langlands.AffineGeneric

open ValuativeRel Matrix LevelZero GeneralLinear JacquetLanglands _root_.Polynomial

universe u

variable {F : Type u} [Field F] [ValuativeRel F] {m : ℕ}

/-- For a uniformizer `ϖ`, if `D(γ) ≠ 0` for `γ ∈ I⁺`, then `det(γ - 1)` has the
valuation of `ϖ`. -/
theorem val_det_sub_one_eq {ϖ : Fˣ} (hϖ : Iwasawa.IsUniformizingElement (valuation F) ϖ)
    {γ : GeneralLinear (m + 1) F} (hγ : γ ∈ iwahoriRadical m) (hD : coordProd ϖ γ ≠ 0) :
    valuation F ((γ : Matrix (Fin (m + 1)) (Fin (m + 1)) F) - 1).det =
      valuation F (ϖ : F) := by
  rw [coordProd_eq hϖ hγ] at hD
  set d := ((γ : Matrix (Fin (m + 1)) (Fin (m + 1)) F) - 1).det
  have hx : valuation F ((-1) ^ m * ((ϖ : F)⁻¹ * d)) ≤ 1 := by
    by_contra h
    exact hD (resOf_of_not_le_one h)
  have h1 := val_eq_one_of_resOf_ne_zero hx hD
  have hϖ0 : valuation F (ϖ : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr ϖ.ne_zero
  simp only [map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul, map_inv₀] at h1
  calc valuation F d = valuation F (ϖ : F) * ((valuation F (ϖ : F))⁻¹ * valuation F d) := by
        rw [← mul_assoc, mul_inv_cancel₀ hϖ0, one_mul]
    _ = valuation F (ϖ : F) := by rw [h1, mul_one]

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]

/-- **Regular ellipticity.** For a uniformizer `ϖ` and characteristic-zero local field `F`,
if `γ ∈ I⁺` and `D(γ) ≠ 0`, then its characteristic polynomial is irreducible and separable. -/
theorem isRegularElliptic_of_coordProd_ne_zero {ϖ : Fˣ}
    (hϖ : Iwasawa.IsUniformizingElement (valuation F) ϖ) {γ : GeneralLinear (m + 1) F}
    (hγ : γ ∈ iwahoriRadical m) (hD : coordProd ϖ γ ≠ 0) : IsRegularElliptic γ := by
  set Y : Matrix (Fin (m + 1)) (Fin (m + 1)) F :=
    (γ : Matrix (Fin (m + 1)) (Fin (m + 1)) F) - 1 with hYdef
  have hY : IsIwahoriRadical Y := hγ.1
  let Y' : Matrix (Fin (m + 1)) (Fin (m + 1)) (integers F) := fun i j =>
    ⟨Y i j, (Valuation.mem_integer_iff _ _).mpr (hY i j).1⟩
  have hY' : Y'.map (algebraMap (integers F) F) = Y := by
    ext i j
    rfl
  set p := Y'.charpoly with hp
  have hm : p.Monic := Y'.charpoly_monic
  have hd : p.natDegree = m + 1 := by
    rw [hp, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hres : ∀ i j, j ≤ i → IsLocalRing.residue (integers F) (Y' i j) = 0 := by
    intro i j hij
    rw [IsLocalRing.residue_eq_zero_iff, LevelZero.mem_maximalIdeal_iff]
    exact (hY i j).2 hij
  have hred : p.map (IsLocalRing.residue (integers F)) = X ^ (m + 1) := by
    rw [hp, ← Matrix.charpoly_map, Matrix.charpoly_of_isUpperTriangular]
    · simp only [Matrix.map_apply, hres _ _ le_rfl, map_zero, sub_zero, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
    · intro i j hij
      simp only [Matrix.map_apply]
      exact hres i j (le_of_lt hij)
  have hcoeff : ∀ {i}, i < p.natDegree → p.coeff i ∈ IsLocalRing.maximalIdeal (integers F) := by
    intro i hi
    rw [hd] at hi
    have h := congrArg (fun q => q.coeff i) hred
    simp only [Polynomial.coeff_map, Polynomial.coeff_X_pow, hi.ne, ↓reduceIte] at h
    exact (IsLocalRing.residue_eq_zero_iff _).mp h
  have hdet : ((Y'.det : integers F) : F) = Y.det := by
    change algebraMap (integers F) F Y'.det = Y.det
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hY']
  have hvdet : valuation F Y.det = valuation F (ϖ : F) := val_det_sub_one_eq hϖ hγ hD
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (integers F)
  have hπ1 : valuation F (π : F) < 1 :=
    (LevelZero.mem_maximalIdeal_iff F π).mp
      ((IsLocalRing.mem_maximalIdeal _).mpr hπ.not_isUnit)
  have hnot : p.coeff 0 ∉ (IsLocalRing.maximalIdeal (integers F)) ^ 2 := by
    intro hmem
    have hcoeff0 : Y'.det = (-1) ^ (m + 1) * p.coeff 0 := by
      rw [Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin]
    have hdetmem : Y'.det ∈ (IsLocalRing.maximalIdeal (integers F)) ^ 2 := by
      rw [hcoeff0]
      exact Ideal.mul_mem_left _ _ hmem
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hdetmem
    obtain ⟨a, ha⟩ := hdetmem
    have hv : valuation F Y.det ≤ valuation F (π : F) * valuation F (π : F) := by
      rw [← hdet, ha]
      push_cast
      rw [map_mul, map_pow, pow_two]
      exact mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).mp a.2)
    have hπϖ : valuation F (π : F) ≤ valuation F (ϖ : F) := val_le_uniformizer hϖ hπ1
    have hϖ0 : valuation F (ϖ : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr ϖ.ne_zero
    have hlt : valuation F (ϖ : F) * valuation F (ϖ : F) < valuation F (ϖ : F) := by
      calc valuation F (ϖ : F) * valuation F (ϖ : F) < valuation F (ϖ : F) * 1 :=
            mul_lt_mul_of_pos_left hϖ.1 (zero_lt_iff.mpr hϖ0)
        _ = valuation F (ϖ : F) := mul_one _
    have := (hv.trans (mul_le_mul' hπϖ hπϖ)).trans_lt hlt
    rw [hvdet] at this
    exact lt_irrefl _ this
  have he : p.IsEisensteinAt (IsLocalRing.maximalIdeal (integers F)) :=
    hm.isEisensteinAt_of_mem_of_notMem (Ideal.IsPrime.ne_top inferInstance) hcoeff hnot
  have hirr : Irreducible (p.map (algebraMap (integers F) F)) :=
    (hm.irreducible_iff_irreducible_map_fraction_map (K := F)).mp
      (he.irreducible inferInstance hm.isPrimitive (by rw [hd]; exact Nat.succ_pos m))
  have hYc : Y.charpoly = p.map (algebraMap (integers F) F) := by
    rw [← hY', Matrix.charpoly_map]
  have hγc : (γ : Matrix (Fin (m + 1)) (Fin (m + 1)) F).charpoly =
      taylorEquiv (-1 : F) Y.charpoly := by
    have hγY : (γ : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
        Y - Matrix.scalar (Fin (m + 1)) (-1 : F) := by
      rw [map_neg, map_one, sub_neg_eq_add, hYdef, sub_add_cancel]
    rw [hγY, Matrix.charpoly_sub_scalar]
    exact (taylor_apply (-1 : F) Y.charpoly).symm
  have hirrγ : Irreducible (γ : Matrix (Fin (m + 1)) (Fin (m + 1)) F).charpoly := by
    rw [hγc, MulEquiv.irreducible_iff, hYc]
    exact hirr
  exact ⟨PerfectField.separable_of_irreducible hirrγ, hirrγ⟩

/-- For a uniformizer `ϖ` and characteristic-zero local field `F`, if `γ ∈ I⁺` and
`D(γ) ≠ 0`, then `γ` is regular semisimple. -/
theorem isRegularSemisimple_of_coordProd_ne_zero {ϖ : Fˣ}
    (hϖ : Iwasawa.IsUniformizingElement (valuation F) ϖ) {γ : GeneralLinear (m + 1) F}
    (hγ : γ ∈ iwahoriRadical m) (hD : coordProd ϖ γ ≠ 0) : IsRegularSemisimple γ :=
  (isRegularElliptic_of_coordProd_ne_zero hϖ hγ hD).isRegularSemisimple

end Langlands.AffineGeneric
