import Langlands.Global.AdelicLineCharacterHeight
import Langlands.Global.AdelicOrbitHeightCompactBounds
import Langlands.Global.AdelicIwasawaHeight
import Langlands.Global.AdelicSiegelDiagonalHeightBound
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization

/-! # Iwasawa character values and rational projective orbit heights -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Matrix NNReal

set_option autoImplicit false

namespace Langlands.Global.PrimitiveAdelicHeight

private theorem pi_norm_eq_iSup {I E : Type*} [Fintype I] [SeminormedAddGroup E]
    (x : I → E) : ‖x‖ = ⨆ i, ‖x i‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (Real.iSup_nonneg fun i => norm_nonneg (x i))).mpr
    intro i
    exact Finite.le_ciSup_of_le i le_rfl
  · exact Real.iSup_le (fun i => norm_le_pi_norm x i) (norm_nonneg x)

/-- The principal vector height is Mathlib's multiplicative coordinate height. -/
theorem height_rational_eq_mulHeight (F : Type u) [Field F] [NumberField F] {n : ℕ}
    {v : Fin n → F} (hv : v ≠ 0) : height F n (rational F n v) = Height.mulHeight v := by
  rw [height, Height.mulHeight_eq hv, NumberField.prod_archAbsVal_eq]
  congr 1
  · apply Finset.prod_congr rfl
    intro w _
    simp only [infiniteNorm, pi_norm_eq_iSup, rational,
      AdelicSiegelFactors.norm_infiniteProjection_diagonal]
    rfl
  · change (∏ᶠ w : FinitePlace F, finiteNorm F n (rational F n v) w) =
      ∏ᶠ w : NumberField.FinitePlace F, ⨆ i : Fin n, w (v i)
    simp only [finiteNorm, pi_norm_eq_iSup, rational,
      AdelicSiegelFactors.norm_finiteProjection_diagonal]
    exact finprod_comp_equiv NumberField.FinitePlace.equivHeightOneSpectrum.symm
      (f := fun w : NumberField.FinitePlace F => ⨆ i : Fin n, w (v i))

end Langlands.Global.PrimitiveAdelicHeight

namespace Langlands.Global.RepresentationGrowth

open Langlands.GroupScheme AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} {n : ℕ}
  (ρ : MatrixRepresentation G (Fin n)) {v : Fin n → F} (hv : v ≠ 0)

/-- The projective point obtained by applying the rational representation to a fixed
nonzero rational vector. -/
def rationalOrbitPoint (x : RationalGroupPoints F G) : Projectivization F (Fin n → F) :=
  Projectivization.mk F ((rationalMatrix F G ρ x).val *ᵥ v)
    (PrimitiveAdelicHeight.rational_mulVec_ne_zero F n _ hv)

/-- On a rational group point, the adelic orbit height equals the projective height
of the corresponding rational orbit point. -/
theorem orbitHeight_rational_eq_mulHeight (x : RationalGroupPoints F G) :
    orbitHeight F G ρ v (rational F G x) = (rationalOrbitPoint ρ hv x).mulHeight := by
  rw [← one_mul (rational F G x), orbitHeight_mul_rational]
  rw [rationalOrbitPoint, Projectivization.mulHeight_mk]
  simp only [orbitHeight, PrimitiveAdelicHeight.rationalHeight, map_one, Units.val_one,
    Matrix.one_mulVec]
  exact PrimitiveAdelicHeight.height_rational_eq_mulHeight F
    (PrimitiveAdelicHeight.rational_mulVec_ne_zero F n _ hv)

variable [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}

/-- The character of an adelic eigenvector gives its exact Iwasawa projective height formula. -/
theorem orbitHeight_rational_inv_mul_exp_height (hK : IsIwasawaCompact p K)
    (χ : rationalCharacters P)
    (ha : ∀ q : AdelicGroupPoints F P,
      (adelicMatrix F G ρ (map F P G p q)).val *ᵥ PrimitiveAdelicHeight.rational F n v =
        (character F P χ.toMul q).val • PrimitiveAdelicHeight.rational F n v)
    (x : RationalGroupPoints F G) :
    ∃ k ∈ K, (rationalOrbitPoint ρ hv x⁻¹).mulHeight *
        Real.exp (hK.height (rational F G x) χ) = orbitHeight F G ρ v k⁻¹ := by
  obtain ⟨q, k, hk, hqk⟩ := hK.exists_eq (rational F G x)
  have hInv : rational F G x⁻¹ = k⁻¹ * map F P G p q⁻¹ := by
    rw [map_inv, ← hqk, mul_inv_rev, map_inv]
  refine ⟨k, hk, ?_⟩
  rw [← orbitHeight_rational_eq_mulHeight ρ hv, hInv,
    orbitHeight_mul_eq_of_idele_scalar F G ρ v hv _ _ _ (ha q⁻¹), hK.height_eq hk hqk,
    characterLog_apply]
  let t : ℝ≥0ˣ := characterNorm F P χ.toMul q
  have ht : 0 < ((t : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr t.ne_zero)
  change ((characterNorm F P χ.toMul q⁻¹ : ℝ≥0) : ℝ) * _ *
    Real.exp (Real.log ((t : ℝ≥0) : ℝ)) = _
  rw [map_inv, Real.exp_log ht, Units.val_inv_eq_inv_val, NNReal.coe_inv]
  change ((t : ℝ≥0) : ℝ)⁻¹ * _ * ((t : ℝ≥0) : ℝ) = _
  rw [mul_right_comm, inv_mul_cancel₀ ht.ne', one_mul]

/-- On rational points every such Iwasawa character is bounded above by a constant
minus the logarithmic height of the corresponding inverse orbit point. -/
theorem exists_height_le_sub_log_mulHeight (hK : IsIwasawaCompact p K)
    (χ : rationalCharacters P)
    (ha : ∀ q : AdelicGroupPoints F P,
      (adelicMatrix F G ρ (map F P G p q)).val *ᵥ PrimitiveAdelicHeight.rational F n v =
        (character F P χ.toMul q).val • PrimitiveAdelicHeight.rational F n v) :
    ∃ D : ℝ, ∀ x : RationalGroupPoints F G, hK.height (rational F G x) χ ≤
      D - (rationalOrbitPoint ρ hv x⁻¹).logHeight := by
  have hn : 0 < n := by
    obtain ⟨i, _⟩ := Function.ne_iff.mp hv
    exact Nat.zero_lt_of_lt i.isLt
  obtain ⟨B, hB, hbound⟩ := exists_pos_orbitHeight_bounds_of_isCompact F G ρ hn hK.isCompact
  set M := B * orbitHeight F G ρ v 1
  have hM : 0 < M := mul_pos hB (orbitHeight_pos F G ρ hv 1)
  refine ⟨Real.log M, fun x => ?_⟩
  obtain ⟨k, hk, heq⟩ := orbitHeight_rational_inv_mul_exp_height ρ hv hK χ ha x
  have h := (hbound k⁻¹ (K.inv_mem hk) 1 v hv).1
  rw [mul_one, ← heq] at h
  have hlog := Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr
    (mul_pos (Projectivization.mulHeight_pos _) (Real.exp_pos _))) (Set.mem_Ioi.mpr hM) h
  rw [Real.log_mul (Projectivization.mulHeight_ne_zero _) (Real.exp_ne_zero _),
    Real.log_exp, ← Projectivization.logHeight_eq_log_mulHeight] at hlog
  linarith

end Langlands.Global.RepresentationGrowth
