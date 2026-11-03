import Langlands.Representation.Plancherel.SplitTorusCompactKernel
import Langlands.Representation.Plancherel.SplitTorusPositiveCharacter

/-! # The norm formula and uniqueness for all smooth split-torus characters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped TensorProduct CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.SplitTorus

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}

/-- The existing valuation has precisely the common norm kernel. -/
theorem valuation_ker (hA : IsSplitTorus A.toGrp) :
    (valuation hA).ker = rationalCommonNormKernel A.toGrp :=
  BruhatTits.Cartan.centralizerValuation_ker (𝟙 A.toGrp)
    (BruhatTits.Cartan.restrictionEvaluation_id_bijective hA)

/-- Equal classes modulo the common norm kernel have equal actual valuations. -/
theorem valuation_eq_of_mul_inv_mem (hA : IsSplitTorus A.toGrp)
    {a b : rationalPoints A.toGrp}
    (hab : a * b⁻¹ ∈ rationalCommonNormKernel A.toGrp) :
    valuation hA a = valuation hA b := by
  have hk : a * b⁻¹ ∈ (valuation hA).ker := (valuation_ker hA).symm ▸ hab
  have hv : valuation hA (a * b⁻¹) = 1 := hk
  simpa only [map_mul, map_inv, mul_inv_eq_one] using hv

/-- A parameter is determined by its pairing with the actual valuation image. -/
theorem eq_of_pair_valuation_eq (hA : IsSplitTorus A.toGrp)
    {phi psi : RealTorusSpace.Vstar A}
    (h : ∀ a, RealTorusSpace.pair A phi (valuation hA a).toAdd =
      RealTorusSpace.pair A psi (valuation hA a).toAdd) :
    phi = psi := by
  apply (RealTorusSpace.characterDualEquiv hA).injective
  apply AlgebraTensorModule.ext
  intro r c
  change RealTorusSpace.pair A phi (r ⊗ₜ[ℤ] c) =
    RealTorusSpace.pair A psi (r ⊗ₜ[ℤ] c)
  have hc := h (CocharacterUniformizer.latticeSection F A (Multiplicative.ofAdd c))
  rw [valuation_latticeSection] at hc
  rw [show (r ⊗ₜ[ℤ] c : RealTorusSpace.V A) =
    r • ((1 : ℝ) ⊗ₜ[ℤ] c) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
    map_smul, map_smul, hc]

/-- Any parameter satisfying the all-point norm formula is the constructed one.
No smoothness assumption is needed for this uniqueness implication. -/
theorem normalizedRealPart_unique (hA : IsSplitTorus A.toGrp)
    (χ : rationalPoints A.toGrp →* ℂˣ) (phi : RealTorusSpace.Vstar A)
    (hphi : ∀ a, ‖(χ a : ℂ)‖ =
      (LocalField.residueCardinality F : ℝ) ^
        (-RealTorusSpace.pair A phi (valuation hA a).toAdd)) :
    normalizedRealPart hA χ = phi := by
  apply (RealTorusSpace.characterDualEquiv hA).injective
  apply AlgebraTensorModule.ext
  intro r c
  change RealTorusSpace.pair A (normalizedRealPart hA χ) (r ⊗ₜ[ℤ] c) =
    RealTorusSpace.pair A phi (r ⊗ₜ[ℤ] c)
  rw [pair_normalizedRealPart_tmul]
  have hc : sectionLog χ c =
      RealTorusSpace.pair A phi ((1 : ℝ) ⊗ₜ[ℤ] c) := by
    have hs := hphi (CocharacterUniformizer.latticeSection F A (Multiplicative.ofAdd c))
    rw [valuation_latticeSection] at hs
    exact normLog_eq_of_rpow
      (by exact_mod_cast LocalField.residueCardinality_gt_one F) _ _ hs.symm
  rw [hc, show (r ⊗ₜ[ℤ] c : RealTorusSpace.V A) =
    r • ((1 : ℝ) ⊗ₜ[ℤ] c) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
    map_smul, smul_eq_mul]

section CanonicalTopology

variable [IsAffine A.X.left]

local instance pointTopology : TopologicalSpace (rationalPoints A.toGrp) :=
  rationalPointTopology F A.X

/-- Smooth characters have equal moduli on the same common-norm-kernel class. -/
theorem norm_eq_of_mul_inv_mem (hA : IsSplitTorus A.toGrp)
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (rationalPoints A.toGrp)))
    {a b : rationalPoints A.toGrp}
    (hab : a * b⁻¹ ∈ rationalCommonNormKernel A.toGrp) :
    ‖(χ a : ℂ)‖ = ‖(χ b : ℂ)‖ := by
  have hn := norm_eq_one_on_commonNormKernel hA χ hχ hab
  have hd : ‖(χ a : ℂ)‖ / ‖(χ b : ℂ)‖ = 1 := by
    simpa only [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul,
      norm_inv, div_eq_mul_inv] using hn
  exact (div_eq_one_iff_eq (norm_ne_zero_iff.mpr (Units.ne_zero _))).mp hd

/-- The normalized parameter recovers the modulus at every actual rational point. -/
theorem norm_eq_rpow_normalizedRealPart (hA : IsSplitTorus A.toGrp)
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (rationalPoints A.toGrp)))
    (a : rationalPoints A.toGrp) :
    ‖(χ a : ℂ)‖ = (LocalField.residueCardinality F : ℝ) ^
      (-RealTorusSpace.pair A (normalizedRealPart hA χ) (valuation hA a).toAdd) := by
  obtain ⟨c, hc, _⟩ := (CocharacterUniformizer.isUniformizerLatticeSection F A hA).2.2 a
  have hv : (valuation hA (CocharacterUniformizer.latticeSection F A c)).toAdd =
      (1 : ℝ) ⊗ₜ[ℤ] c.toAdd := by
    simpa only [ofAdd_toAdd] using valuation_latticeSection hA c.toAdd
  rw [valuation_eq_of_mul_inv_mem hA hc, hv,
    pair_normalizedRealPart_tmul, one_mul]
  rw [norm_eq_of_mul_inv_mem hA χ hχ hc]
  change ‖(χ (CocharacterUniformizer.latticeSection F A c) : ℂ)‖ =
    (LocalField.residueCardinality F : ℝ) ^ (-normLog
      (LocalField.residueCardinality F) (characterNorm χ
        (CocharacterUniformizer.latticeSection F A (Multiplicative.ofAdd c.toAdd))))
  rw [ofAdd_toAdd]
  exact
    (rpow_neg_normLog (q := (LocalField.residueCardinality F : ℝ))
      (by exact_mod_cast LocalField.residueCardinality_gt_one F)
      (characterNorm χ (CocharacterUniformizer.latticeSection F A c))).symm

/-- The normalized parameter is the normalized logarithmic modulus on the actual image. -/
theorem pair_normalizedRealPart_valuation (hA : IsSplitTorus A.toGrp)
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (rationalPoints A.toGrp)))
    (a : rationalPoints A.toGrp) :
    RealTorusSpace.pair A (normalizedRealPart hA χ) (valuation hA a).toAdd =
      normLog (LocalField.residueCardinality F) (characterNorm χ a) := by
  exact (normLog_eq_of_rpow
    (by exact_mod_cast LocalField.residueCardinality_gt_one F) _ _
    (norm_eq_rpow_normalizedRealPart hA χ hχ a).symm).symm

/-- The separately named raw parameter evaluates to the ordinary natural logarithm. -/
theorem pair_rawLogRealPart_valuation (hA : IsSplitTorus A.toGrp)
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (rationalPoints A.toGrp)))
    (a : rationalPoints A.toGrp) :
    RealTorusSpace.pair A (rawLogRealPart hA χ) (valuation hA a).toAdd =
      Real.log ‖(χ a : ℂ)‖ := by
  rw [rawLogRealPart, map_smul, LinearMap.smul_apply,
    pair_normalizedRealPart_valuation hA χ hχ]
  change -Real.log (LocalField.residueCardinality F : ℝ) *
    (-Real.log ‖(χ a : ℂ)‖ / Real.log (LocalField.residueCardinality F : ℝ)) = _
  have hq : Real.log (LocalField.residueCardinality F : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast LocalField.residueCardinality_gt_one F)).ne'
  field_simp

/-- A smooth character has zero normalized parameter exactly when it is unitary. -/
theorem normalizedRealPart_eq_zero_iff (hA : IsSplitTorus A.toGrp)
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (rationalPoints A.toGrp))) :
    normalizedRealPart hA χ = 0 ↔ ∀ a, ‖(χ a : ℂ)‖ = 1 := by
  constructor
  · intro h a
    simpa [h] using norm_eq_rpow_normalizedRealPart hA χ hχ a
  · intro h
    apply normalizedRealPart_unique hA χ 0
    intro a
    simpa using h a

/-- The constructed parameter together with its proved all-point defining formula. -/
def smoothNormalizedParameter (hA : IsSplitTorus A.toGrp)
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (rationalPoints A.toGrp))) :
    {phi : RealTorusSpace.Vstar A //
      ∀ a, ‖(χ a : ℂ)‖ = (LocalField.residueCardinality F : ℝ) ^
        (-RealTorusSpace.pair A phi (valuation hA a).toAdd)} :=
  ⟨normalizedRealPart hA χ, norm_eq_rpow_normalizedRealPart hA χ hχ⟩

@[simp] theorem smoothNormalizedParameter_val (hA : IsSplitTorus A.toGrp)
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (rationalPoints A.toGrp))) :
    (smoothNormalizedParameter hA χ hχ).val = normalizedRealPart hA χ := rfl

end CanonicalTopology

end Langlands.Plancherel.SplitTorus
