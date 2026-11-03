import Langlands.Geometry.Building.CocharacterUniformizer
import Langlands.BruhatTits.Cartan.CentralizerRealComparison
import Langlands.Representation.Plancherel.RationalImageRealPart

/-! # Normalized real parameters of characters of actual split tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped TensorProduct CategoryTheory.MonObj NNReal
open Langlands.GroupScheme

namespace Langlands.Plancherel.SplitTorus

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}

/-- The existing positive valuation, with no change of construction. -/
abbrev valuation (hA : IsSplitTorus A.toGrp) :=
  BruhatTits.Cartan.centralizerValuation (𝟙 A.toGrp)
    (BruhatTits.Cartan.restrictionEvaluation_id_bijective hA)

/-- The complex modulus of an actual point character, as positive units. -/
def characterNorm (χ : rationalPoints A.toGrp →* ℂˣ) :
    rationalPoints A.toGrp →* ℝ≥0ˣ :=
  (Units.map (nnnormHom : ℂ →*₀ ℝ≥0).toMonoidHom).comp χ

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
@[simp] theorem characterNorm_val (χ : rationalPoints A.toGrp →* ℂˣ)
    (a : rationalPoints A.toGrp) :
    ((characterNorm χ a : ℝ≥0) : ℝ) = ‖(χ a : ℂ)‖ := rfl

/-- The normalized logarithmic modulus on the intrinsic uniformizer section. -/
def sectionLog (χ : rationalPoints A.toGrp →* ℂˣ) :
    cocharacterLattice A →+ ℝ where
  toFun c := normLog (LocalField.residueCardinality F)
    (characterNorm χ (CocharacterUniformizer.latticeSection F A
      (Multiplicative.ofAdd c)))
  map_zero' := by
    change normLog _ (characterNorm χ (CocharacterUniformizer.latticeSection F A 1)) = 0
    rw [map_one, map_one, normLog_one]
  map_add' c d := by
    change normLog _ (characterNorm χ
      (CocharacterUniformizer.latticeSection F A
        (Multiplicative.ofAdd c * Multiplicative.ofAdd d))) = _
    rw [map_mul, map_mul, normLog_mul]

/-- Scalar extension of a real additive functional on the actual cocharacter lattice. -/
def extendLatticeLog (ℓ : cocharacterLattice A →+ ℝ) :
    RealTorusSpace.V A →ₗ[ℝ] ℝ :=
  AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton ℝ (cocharacterLattice A →ₗ[ℤ] ℝ) ℓ.toIntLinearMap)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
@[simp] theorem extendLatticeLog_tmul (ℓ : cocharacterLattice A →+ ℝ)
    (r : ℝ) (c : cocharacterLattice A) :
    extendLatticeLog ℓ (r ⊗ₜ[ℤ] c) = r * ℓ c := rfl

/-- The normalized exponential parameter, transported through the actual perfect pairing. -/
def normalizedRealPart (hA : IsSplitTorus A.toGrp)
    (χ : rationalPoints A.toGrp →* ℂˣ) : RealTorusSpace.Vstar A :=
  (RealTorusSpace.characterDualEquiv hA).symm (extendLatticeLog (sectionLog χ))

theorem pair_normalizedRealPart (hA : IsSplitTorus A.toGrp)
    (χ : rationalPoints A.toGrp →* ℂˣ) (v : RealTorusSpace.V A) :
    RealTorusSpace.pair A (normalizedRealPart hA χ) v =
      extendLatticeLog (sectionLog χ) v := by
  exact LinearMap.congr_fun
    ((RealTorusSpace.characterDualEquiv hA).apply_symm_apply _) v

@[simp] theorem pair_normalizedRealPart_tmul (hA : IsSplitTorus A.toGrp)
    (χ : rationalPoints A.toGrp →* ℂˣ) (r : ℝ) (c : cocharacterLattice A) :
    RealTorusSpace.pair A (normalizedRealPart hA χ) (r ⊗ₜ[ℤ] c) =
      r * sectionLog χ c := by
  rw [pair_normalizedRealPart, extendLatticeLog_tmul]

/-- The raw natural-logarithm parameter, with its separate source normalization. -/
def rawLogRealPart (hA : IsSplitTorus A.toGrp)
    (χ : rationalPoints A.toGrp →* ℂˣ) : RealTorusSpace.Vstar A :=
  (-Real.log (LocalField.residueCardinality F : ℝ)) • normalizedRealPart hA χ

theorem rawLogRealPart_eq (hA : IsSplitTorus A.toGrp)
    (χ : rationalPoints A.toGrp →* ℂˣ) :
    rawLogRealPart hA χ =
      (-Real.log (LocalField.residueCardinality F : ℝ)) • normalizedRealPart hA χ := rfl

private theorem log_residueCardinality_ne_zero :
    Real.log (LocalField.residueCardinality F : ℝ) ≠ 0 := by
  apply (Real.log_pos _).ne'
  exact_mod_cast LocalField.residueCardinality_gt_one F

/-- The raw parameter has precisely the ordinary log modulus on section points. -/
theorem pair_rawLogRealPart_tmul_one (hA : IsSplitTorus A.toGrp)
    (χ : rationalPoints A.toGrp →* ℂˣ) (c : cocharacterLattice A) :
    RealTorusSpace.pair A (rawLogRealPart hA χ) ((1 : ℝ) ⊗ₜ[ℤ] c) =
      Real.log ‖(χ (CocharacterUniformizer.latticeSection F A
        (Multiplicative.ofAdd c)) : ℂ)‖ := by
  rw [rawLogRealPart, map_smul, LinearMap.smul_apply,
    pair_normalizedRealPart_tmul, one_mul]
  change -Real.log (LocalField.residueCardinality F : ℝ) *
    (-Real.log ‖(χ (CocharacterUniformizer.latticeSection F A
      (Multiplicative.ofAdd c)) : ℂ)‖ /
        Real.log (LocalField.residueCardinality F : ℝ)) = _
  field_simp [log_residueCardinality_ne_zero (F := F)]

theorem normalizedRealPart_one (hA : IsSplitTorus A.toGrp) :
    normalizedRealPart hA (1 : rationalPoints A.toGrp →* ℂˣ) = 0 := by
  apply (RealTorusSpace.characterDualEquiv hA).injective
  apply AlgebraTensorModule.ext
  intro r c
  change RealTorusSpace.pair A (normalizedRealPart hA 1) (r ⊗ₜ[ℤ] c) = 0
  rw [pair_normalizedRealPart_tmul]
  simp [sectionLog, characterNorm, normLog]

theorem normalizedRealPart_mul (hA : IsSplitTorus A.toGrp)
    (χ ψ : rationalPoints A.toGrp →* ℂˣ) :
    normalizedRealPart hA (χ * ψ) =
      normalizedRealPart hA χ + normalizedRealPart hA ψ := by
  apply (RealTorusSpace.characterDualEquiv hA).injective
  apply AlgebraTensorModule.ext
  intro r c
  change RealTorusSpace.pair A (normalizedRealPart hA (χ * ψ)) (r ⊗ₜ[ℤ] c) =
    RealTorusSpace.pair A (normalizedRealPart hA χ + normalizedRealPart hA ψ)
      (r ⊗ₜ[ℤ] c)
  rw [map_add, LinearMap.add_apply, pair_normalizedRealPart_tmul,
    pair_normalizedRealPart_tmul, pair_normalizedRealPart_tmul, ← mul_add]
  congr 1
  change normLog _ (characterNorm (χ * ψ) _) = _
  have hn (a : rationalPoints A.toGrp) :
      characterNorm (χ * ψ) a = characterNorm χ a * characterNorm ψ a := by
    apply Units.ext
    change ‖((χ a : ℂ) * (ψ a : ℂ))‖₊ = _
    exact nnnorm_mul _ _
  rw [hn, normLog_mul]
  rfl

theorem normalizedRealPart_inv (hA : IsSplitTorus A.toGrp)
    (χ : rationalPoints A.toGrp →* ℂˣ) :
    normalizedRealPart hA χ⁻¹ = -normalizedRealPart hA χ := by
  have h := normalizedRealPart_mul hA χ χ⁻¹
  rw [show χ * χ⁻¹ = 1 by ext a; simp,
    normalizedRealPart_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

end Langlands.Plancherel.SplitTorus
