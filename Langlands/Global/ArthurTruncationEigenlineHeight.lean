import Langlands.Global.AdelicIwasawaOrbitHeight
import Langlands.Global.AdelicOrbitHeightCompactBounds

/-! # An eigenline comparison of two Iwasawa logarithms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix NNReal

namespace Langlands.Global.ArthurTruncation.Idempotence

open Langlands.GroupScheme AdelicGroupPoints RepresentationGrowth

/-- An invertible coordinate of a primitive vector has idelic norm at most the
primitive-vector height. The norms at every place use the same normalization. -/
theorem ideleNorm_le_primitiveHeight {F : Type u} [Field F] [NumberField F] {d : ℕ}
    {v : PrimitiveAdelicHeight.Vector F d} (hv : PrimitiveAdelicHeight.IsPrimitive F d v)
    (j : Fin d) (z : Ideles F) (hz : z.val = v j) :
    ((IdeleAbsoluteValue.full F z : ℝ≥0) : ℝ) ≤ PrimitiveAdelicHeight.height F d v := by
  rw [IdeleAbsoluteValue.coe_full, PrimitiveAdelicHeight.height]
  refine mul_le_mul ?_ ?_ (finprod_nonneg fun _ => norm_nonneg _)
    (Finset.prod_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _)
  · refine Finset.prod_le_prod₀ (fun _ _ => pow_nonneg (norm_nonneg _) _) fun place _ => ?_
    apply pow_le_pow_left₀ (norm_nonneg _)
    change ‖infiniteProjection F place z.val‖ ≤ ‖fun l : Fin d => infiniteProjection F place (v l)‖
    rw [hz]
    exact norm_le_pi_norm (fun l : Fin d => infiniteProjection F place (v l)) j
  · have hfin : (fun p : FinitePlace F => ‖z.val.2 p‖).HasFiniteMulSupport :=
      NumberField.FiniteAdeleRing.hasFiniteMulSupport_norm (ideleProductEquiv F z).2
    refine finprod_le_finprod₀ hfin (fun _ => norm_nonneg _) (hv.hasFiniteMulSupport F d) ?_
    intro place
    change ‖finiteProjection F place z.val‖ ≤ ‖fun l : Fin d => finiteProjection F place (v l)‖
    rw [hz]
    exact norm_le_pi_norm (fun l : Fin d => finiteProjection F place (v l)) j

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)

private theorem characterNorm_exp_height (χ : rationalCharacters P)
    {q : AdelicGroupPoints F P} {k x : AdelicGroupPoints F G}
    (hk : k ∈ K) (hx : map F P G p q * k = x) :
    ((characterNorm F P χ.toMul q⁻¹ : ℝ≥0) : ℝ) = Real.exp (-hK.height x χ) := by
  rw [hK.height_eq hk hx, characterLog_apply, map_inv, Units.val_inv_eq_inv_val,
    NNReal.coe_inv, Real.exp_neg, Real.exp_log]
  exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (characterNorm F P χ.toMul q).ne_zero)

/-- Compare Iwasawa logarithms through two rational vectors in an actual representation.
The first vector is a parabolic eigenvector. For the second vector one specified
coordinate records the second parabolic character. Compactness of the Iwasawa
subgroup bounds the effect of the two compact factors. -/
theorem exists_heightCharacter_le_add_of_orbit_eq {d : ℕ} (ρ : MatrixRepresentation G (Fin d))
    {v₁ v₂ : Fin d → F} (hv₁ : v₁ ≠ 0) (j : Fin d) (hv₂j : v₂ j ≠ 0)
    (χ₁ χ₂ : rationalCharacters P)
    (h₁ : ∀ q : AdelicGroupPoints F P,
      (adelicMatrix F G ρ (map F P G p q)).val *ᵥ PrimitiveAdelicHeight.rational F d v₁ =
        (character F P χ₁.toMul q).val • PrimitiveAdelicHeight.rational F d v₁)
    (h₂ : ∀ q : AdelicGroupPoints F P,
      ((adelicMatrix F G ρ (map F P G p q)).val *ᵥ PrimitiveAdelicHeight.rational F d v₂) j =
        (character F P χ₂.toMul q).val * algebraMap F (Adeles F) (v₂ j)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x y : AdelicGroupPoints F G,
      (adelicMatrix F G ρ x⁻¹).val *ᵥ PrimitiveAdelicHeight.rational F d v₁ =
        (adelicMatrix F G ρ y⁻¹).val *ᵥ PrimitiveAdelicHeight.rational F d v₂ →
      hK.height x χ₁ ≤ hK.height y χ₂ + B := by
  have hv₂ : v₂ ≠ 0 := fun h => hv₂j (congrFun h j)
  obtain ⟨b, hb, hdist⟩ :=
    exists_pos_orbitHeight_bounds_of_isCompact F G ρ (Nat.zero_lt_of_lt j.isLt) hK.isCompact
  let M := b * (b * orbitHeight F G ρ v₁ 1)
  have hM : 0 < M := mul_pos hb (mul_pos hb (orbitHeight_pos F G ρ hv₁ 1))
  refine ⟨max (Real.log M) 0, le_max_right _ _, fun x y heq => ?_⟩
  obtain ⟨q₁, k₁, hk₁, hx⟩ := hK.exists_eq x
  obtain ⟨q₂, k₂, hk₂, hy⟩ := hK.exists_eq y
  have hx' : x⁻¹ = k₁⁻¹ * map F P G p q₁⁻¹ := by rw [← hx, mul_inv_rev, map_inv]
  have hy' : y⁻¹ = k₂⁻¹ * map F P G p q₂⁻¹ := by rw [← hy, mul_inv_rev, map_inv]
  have horbit : orbitHeight F G ρ v₁ x⁻¹ = orbitHeight F G ρ v₂ y⁻¹ :=
    congrArg (PrimitiveAdelicHeight.height F d) heq
  have h1 :
      orbitHeight F G ρ v₁ x⁻¹ ≤
        Real.exp (-hK.height x χ₁) * (b * orbitHeight F G ρ v₁ 1) := by
    rw [hx', orbitHeight_mul_eq_of_idele_scalar F G ρ v₁ hv₁ _ _ _ (h₁ q₁⁻¹)]
    change ((characterNorm F P χ₁.toMul q₁⁻¹ : ℝ≥0) : ℝ) * orbitHeight F G ρ v₁ k₁⁻¹ ≤ _
    rw [characterNorm_exp_height hK χ₁ hk₁ hx]
    exact mul_le_mul_of_nonneg_left (by
      simpa only [mul_one] using (hdist k₁⁻¹ (K.inv_mem hk₁) 1 v₁ hv₁).1)
      (Real.exp_nonneg _)
  let z := (adelicMatrix F G ρ (map F P G p q₂⁻¹)).val *ᵥ PrimitiveAdelicHeight.rational F d v₂
  have hz : PrimitiveAdelicHeight.IsPrimitive F d z := ⟨_, v₂, hv₂, rfl⟩
  let c := diagonalUnits F (Units.mk0 (v₂ j) hv₂j)
  have hval : (character F P χ₂.toMul q₂⁻¹ * c).val = z j := (h₂ q₂⁻¹).symm
  have hcoord := ideleNorm_le_primitiveHeight hz j (character F P χ₂.toMul q₂⁻¹ * c) hval
  rw [map_mul, show IdeleAbsoluteValue.full F c = 1 from IdeleAbsoluteValue.full_diagonalUnits _ _, mul_one]
    at hcoord
  change ((characterNorm F P χ₂.toMul q₂⁻¹ : ℝ≥0) : ℝ) ≤
    orbitHeight F G ρ v₂ (map F P G p q₂⁻¹) at hcoord
  rw [characterNorm_exp_height hK χ₂ hk₂ hy] at hcoord
  have h2 : orbitHeight F G ρ v₂ (map F P G p q₂⁻¹) ≤ b * orbitHeight F G ρ v₂ y⁻¹ := by
    rw [hy']
    exact (hdist k₂⁻¹ (K.inv_mem hk₂) (map F P G p q₂⁻¹) v₂ hv₂).2
  have hcmp : Real.exp (-hK.height y χ₂) ≤ M * Real.exp (-hK.height x χ₁) := by
    calc
      _ ≤ _ := hcoord.trans h2
      _ ≤ b * (Real.exp (-hK.height x χ₁) * (b * orbitHeight F G ρ v₁ 1)) := by
        rw [← horbit]
        exact mul_le_mul_of_nonneg_left h1 hb.le
      _ = _ := by unfold M; ring
  have hlog := Real.log_le_log (Real.exp_pos _) hcmp
  rw [Real.log_exp, Real.log_mul hM.ne' (Real.exp_ne_zero _), Real.log_exp] at hlog
  have hle := le_max_left (Real.log M) 0
  linarith

end Langlands.Global.ArthurTruncation.Idempotence
