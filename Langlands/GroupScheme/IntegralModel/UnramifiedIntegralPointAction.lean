import Langlands.GroupScheme.IntegralModel.IntegralPointAutomorphisms
import Langlands.GroupScheme.IntegralModel.UnramifiedModelDescent

/-! # Conjugation on the original unramified integral image -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

open Langlands.LocalGalois Langlands.LocalGalois.Separable GaloisPointComparison
open Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  (M : IntegralModel ↥𝒪[F] F G)

local instance : NontriviallyNormedField F := localNormedField F
local instance : IsUltrametricDist F := localNormedField_ultrametric F
local instance : CompleteSpace F := localNormedField_complete F

local instance : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance : IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

private theorem mem_unramifiedIntegerRange (x : inertiaFixedField F) :
    x ∈ Set.range (algebraMap (fixedFieldIntegers F) (inertiaFixedField F)) ↔
      fixedFieldValuation F x ≤ 1 := by
  constructor
  · rintro ⟨a, rfl⟩
    exact a.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- Every base-field automorphism of the actual inertia fixed field preserves
and reflects its actual integer ring. -/
theorem unramifiedIntegerRange_conjugate_iff
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (x : inertiaFixedField F) :
    σ x ∈ Set.range (algebraMap (fixedFieldIntegers F) (inertiaFixedField F)) ↔
      x ∈ Set.range (algebraMap (fixedFieldIntegers F) (inertiaFixedField F)) := by
  rw [mem_unramifiedIntegerRange, mem_unramifiedIntegerRange,
    fixedFieldValuation_eq_spectralValuation]
  have h : spectralValuation F (inertiaFixedField F) (σ x) =
      spectralValuation F (inertiaFixedField F) x :=
    NNReal.eq (spectralNorm_eq_of_equiv σ x).symm
  rw [h]

/-- Actual coefficient conjugation preserves and reflects the original model's
integral image after unramified base change. -/
theorem mem_baseChangeUnramified_integralPoints_rationalConjugate_iff
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (g : rationalPoints (baseChanged F (inertiaFixedField F) G)) :
    rationalConjugate F (inertiaFixedField F) G σ g ∈
        M.baseChangeUnramified.integralPoints ↔
      g ∈ M.baseChangeUnramified.integralPoints :=
  M.mem_baseChange_integralPoints_rationalConjugate_iff
    (fixedFieldIntegers F) (inertiaFixedField F) σ
    (unramifiedIntegerRange_conjugate_iff σ) g

/-- The actual coefficient Galois group acts by automorphisms of the integral
image of the original model over the actual unramified integer ring. -/
def unramifiedIntegralPointAction :
    (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →*
      MulAut M.baseChangeUnramified.integralPoints where
  toFun σ := M.baseChangeIntegralPointAut
    (fixedFieldIntegers F) (inertiaFixedField F) σ
    (unramifiedIntegerRange_conjugate_iff σ)
  map_one' := by
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    exact rationalConjugate_one F (inertiaFixedField F) G g.val
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    exact rationalConjugate_mul F (inertiaFixedField F) G σ τ g.val

@[simp] theorem unramifiedIntegralPointAction_coe
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (g : M.baseChangeUnramified.integralPoints) :
    (M.unramifiedIntegralPointAction σ g :
        rationalPoints (baseChanged F (inertiaFixedField F) G)) =
      rationalConjugate F (inertiaFixedField F) G σ g := rfl

variable [IsAffineHom G.X.hom]

private instance unramifiedExtensionAffineHom :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- A compatible semilinear map on the actual upstairs quotient preserves the
fixed locus of the original extended model image. The quotient map is supplied. -/
theorem unramifiedIntegralImage_fixed_map
    (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (e : C.ReducedBuilding → C.ReducedBuilding)
    (he : ∀ (g : rationalPoints (baseChanged F (inertiaFixedField F) G))
      (z : C.ReducedBuilding),
      e (g • z) = rationalConjugate F (inertiaFixedField F) G σ g • e z)
    (x : C.ReducedBuilding)
    (hx : ∀ g : rationalPoints (baseChanged F (inertiaFixedField F) G),
      g ∈ M.baseChangeUnramified.integralPoints → g • x = x) :
    ∀ g : rationalPoints (baseChanged F (inertiaFixedField F) G),
      g ∈ M.baseChangeUnramified.integralPoints → g • e x = e x := by
  intro g hg
  let a := (M.unramifiedIntegralPointAction σ).symm ⟨g, hg⟩
  have ha : rationalConjugate F (inertiaFixedField F) G σ a.val = g := by
    exact congrArg Subtype.val
      ((M.unramifiedIntegralPointAction σ).apply_symm_apply ⟨g, hg⟩)
  rw [← ha, ← he, hx a.val a.property]

/-- The unique point fixed by the original extended integral image is fixed
by every supplied compatible semilinear quotient map. -/
theorem unramifiedIntegralImage_map_eq_of_unique_fixed
    (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (e : C.ReducedBuilding → C.ReducedBuilding)
    (he : ∀ (g : rationalPoints (baseChanged F (inertiaFixedField F) G))
      (z : C.ReducedBuilding),
      e (g • z) = rationalConjugate F (inertiaFixedField F) G σ g • e z)
    (x : C.ReducedBuilding)
    (hx : ∀ g : rationalPoints (baseChanged F (inertiaFixedField F) G),
      g ∈ M.baseChangeUnramified.integralPoints → g • x = x)
    (hunique : ∀ y : C.ReducedBuilding,
      (∀ g : rationalPoints (baseChanged F (inertiaFixedField F) G),
        g ∈ M.baseChangeUnramified.integralPoints → g • y = y) → y = x) :
    e x = x :=
  hunique (e x) (M.unramifiedIntegralImage_fixed_map C σ e he x hx)

end Langlands.GroupScheme.IntegralModel
