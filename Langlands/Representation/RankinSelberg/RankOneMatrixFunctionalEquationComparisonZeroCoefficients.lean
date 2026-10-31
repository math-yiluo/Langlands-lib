import Langlands.Representation.GodementJacquet.Zeta
import Langlands.Representation.RankinSelberg.RankOneCharacterReductionProof
import Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonZero

/-!
# Actual smooth matrix coefficients of a rank-one Whittaker model

Evaluation at the identity is a linear equivalence from a rank-one coefficient
model to the complex numbers. Smoothness of this line makes every algebraic
functional smooth. Thus its actual bi-smooth matrix coefficient space is exactly
the space of underlying model functions.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker

universe uF uV uG

section Lines

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A nonzero linear form on a complex line is bijective. -/
theorem linearForm_bijective_of_complexLine (L : V ≃ₗ[ℂ] ℂ)
    (ℓ : Module.Dual ℂ V) (hℓ : ℓ ≠ 0) : Function.Bijective ℓ := by
  have hcoord (v : V) : ℓ v = L v * ℓ (L.symm 1) := by
    conv_lhs => rw [eq_coord_smul_symm_one L v]
    rw [map_smul, smul_eq_mul]
  have hz : ℓ (L.symm 1) ≠ 0 := by
    intro hz
    apply hℓ
    ext v
    rw [hcoord, hz, mul_zero]
    rfl
  constructor
  · intro v w hvw
    apply L.injective
    exact mul_right_cancel₀ hz ((hcoord v).symm.trans (hvw.trans (hcoord w)))
  · intro z
    refine ⟨(z / ℓ (L.symm 1)) • L.symm 1, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hz]

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- A smooth action on a complex line is trivial on one open subgroup. -/
theorem exists_openSubgroup_all_fixed_of_complexLine
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (L : V ≃ₗ[ℂ] ℂ) :
    ∃ K : OpenSubgroup G, ∀ k : K, ∀ v : V, ρ (k : G) v = v := by
  obtain ⟨K, hK⟩ := hρ (L.symm 1)
  refine ⟨K, fun k v => ?_⟩
  have hv := eq_coord_smul_symm_one L v
  have hk : ρ (k : G) (L.symm 1) = L.symm 1 := hK k
  rw [hv, map_smul, hk]

/-- On a smooth complex line, any algebraic functional is a smooth functional. -/
def smoothDualOfComplexLine (ρ : Representation ℂ G V)
    (hρ : IsSmooth ρ) (L : V ≃ₗ[ℂ] ℂ) (ℓ : Module.Dual ℂ V) : SmoothDual ρ :=
  ⟨ℓ, by
    obtain ⟨K, hK⟩ := exists_openSubgroup_all_fixed_of_complexLine ρ hρ L
    refine ⟨K, fun k => ?_⟩
    apply LinearMap.ext
    intro v
    change ℓ (ρ (k : G)⁻¹ v) = ℓ v
    rw [hK ⟨(k : G)⁻¹, K.inv_mem k.property⟩ v]⟩

end Lines

section RankOne

variable {F : Type uF} [Field F] [TopologicalSpace F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F)
  (σ : Representation ℂ (Langlands.GeneralLinear (0 + 1) F) V)
  (hσ : IsOfWhittakerType 0 (standardCharacter ψ 0) σ)
  (ℓ : glFunctionals ψ 0 σ) (hℓ : ℓ.val ≠ 0)

/-- The original carrier of a full rank-one Whittaker-type representation is
a complex line, using its entire algebraic dual. -/
def rankOneCarrierComplexLine : V ≃ₗ[ℂ] ℂ := by
  let e := Classical.choice hσ.2.2
  let D : Module.Dual ℂ V ≃ₗ[ℂ] ℂ :=
    (Submodule.topEquiv.symm.trans
      (LinearEquiv.ofEq _ _ (glFunctionals_rankOne ψ σ).symm)).trans e
  exact LinearEquiv.ofBijective (D.symm 1) (dual_symm_one_bijective D)

/-- Evaluation at the identity identifies the actual rank-one coefficient
image with the complex numbers, without assuming irreducibility. -/
def rankOneModelEvaluationEquiv :
    (glCoefficientModel ψ 0 σ ℓ).toSubmodule ≃ₗ[ℂ] ℂ := by
  let L : V ≃ₗ[ℂ] ℂ := LinearEquiv.ofBijective ℓ.val
    (linearForm_bijective_of_complexLine (rankOneCarrierComplexLine ψ σ hσ) ℓ.val hℓ)
  exact
    { toFun := fun w => glModelFunction ψ 0 σ ℓ w 1
      invFun := fun z => modelMap σ ℓ (L.symm z)
      left_inv := by
        intro w
        obtain ⟨v, rfl⟩ := modelMap_surjective σ ℓ w
        change modelMap σ ℓ (L.symm (ℓ.val (σ 1 v))) = modelMap σ ℓ v
        rw [map_one, Module.End.one_apply]
        exact congrArg (modelMap σ ℓ) (L.symm_apply_apply v)
      right_inv := by
        intro z
        change ℓ.val (σ 1 (L.symm z)) = z
        rw [map_one, Module.End.one_apply]
        exact L.apply_symm_apply z
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- The underlying function of a model vector, packaged linearly. -/
def glModelFunctionLinearMap :
    (glCoefficientModel ψ 0 σ ℓ).toSubmodule →ₗ[ℂ]
      (Langlands.GeneralLinear (0 + 1) F → ℂ) where
  toFun := glModelFunction ψ 0 σ ℓ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

include hσ hℓ

/-- Every actual model function is an actual bi-smooth matrix coefficient of
the model representation at rank one. -/
theorem glModelFunction_mem_biSmooth_rankOne
    (w : (glCoefficientModel ψ 0 σ ℓ).toSubmodule) :
    glModelFunction ψ 0 σ ℓ w ∈
      GodementJacquet.biSmoothMatrixCoefficients
        (V := (glCoefficientModel ψ 0 σ ℓ).toSubmodule)
        (glModelRepresentation ψ 0 σ ℓ) := by
  let ρ : Representation ℂ (Langlands.GeneralLinear (0 + 1) F)
      (glCoefficientModel ψ 0 σ ℓ).toSubmodule := glModelRepresentation ψ 0 σ ℓ
  have hρ : IsSmooth (V := (glCoefficientModel ψ 0 σ ℓ).toSubmodule) ρ :=
    glModel_isSmooth ψ 0 σ hσ.1.1 ℓ
  let E := rankOneModelEvaluationEquiv ψ σ hσ ℓ hℓ
  let η := smoothDualOfComplexLine
    (V := (glCoefficientModel ψ 0 σ ℓ).toSubmodule) ρ hρ E E.toLinearMap
  apply Submodule.subset_span
  refine ⟨η, ⟨w, hρ w⟩, funext fun g => ?_⟩
  change glModelFunction ψ 0 σ ℓ (ρ g w) 1 = glModelFunction ψ 0 σ ℓ w g
  rw [glModelFunction_translate, one_mul]

/-- The entire actual bi-smooth coefficient submodule equals the space of
underlying functions of the actual coefficient image at rank one. -/
theorem biSmoothMatrixCoefficients_rankOne_model :
    GodementJacquet.biSmoothMatrixCoefficients
        (V := (glCoefficientModel ψ 0 σ ℓ).toSubmodule)
        (glModelRepresentation ψ 0 σ ℓ) =
      (glModelFunctionLinearMap ψ σ ℓ).range := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨η, v, rfl⟩
    let E := rankOneModelEvaluationEquiv ψ σ hσ ℓ hℓ
    refine ⟨η.val (E.symm 1) • v.val, funext fun g => ?_⟩
    change η.val (E.symm 1) * glModelFunction ψ 0 σ ℓ v.val g =
      η.val (glModelRepresentation ψ 0 σ ℓ g v.val)
    have hv := eq_coord_smul_symm_one E (glModelRepresentation ψ 0 σ ℓ g v.val)
    conv_rhs => rw [hv]
    rw [map_smul, smul_eq_mul]
    change _ = glModelFunction ψ 0 σ ℓ (glModelRepresentation ψ 0 σ ℓ g v.val) 1 *
      η.val (E.symm 1)
    rw [glModelFunction_translate, one_mul, mul_comm]
  · rintro f ⟨w, rfl⟩
    exact glModelFunction_mem_biSmooth_rankOne ψ σ hσ ℓ hℓ w

end RankOne

end Langlands.RankinSelberg
