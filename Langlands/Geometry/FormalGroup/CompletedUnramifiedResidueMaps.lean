import Langlands.Geometry.FormalGroup.UnramifiedCoefficientStages
import Langlands.Geometry.FormalGroup.DrinfeldCoefficientLift

/-! # Completed unramified coefficient maps and residue coordinates on Nilp -/

noncomputable section

set_option maxHeartbeats 1400000

universe u v

open CategoryTheory IsLocalRing ValuativeRel

namespace Langlands.LocalGalois.Separable

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The extension of residue fields supplied by the actual integer inclusion. -/
instance fixedFieldResidueAlgebra : Algebra 𝓀[F] (ResidueField (fixedFieldIntegers F)) :=
  (residueToFixedField F).toAlgebra

instance fixedFieldResidueScalarTower :
    IsScalarTower 𝒪[F] 𝓀[F] (ResidueField (fixedFieldIntegers F)) :=
  IsScalarTower.of_algebraMap_eq fun a => (residueToFixedField_residue F a).symm

/-- The actual completion residue field is modeled by the algebraic closure in
the uncompleted integers, with its specified base residue map. -/
instance fixedFieldResidueAlgClosure : IsAlgClosure 𝓀[F] (ResidueField (fixedFieldIntegers F)) :=
  fixedFieldResidueIsAlgClosure F

end Langlands.LocalGalois.Separable

namespace Langlands.FormalGroup.Nilp

open Langlands.LocalGalois.Separable

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {π : 𝒪[F]}

local notation "C" => fixedFieldIntegers F
local notation "κ" => ResidueField (fixedFieldIntegers F)
local notation "Ĉ" => CompletedUnramifiedIntegers F
local notation "σ₀" => IsScalarTower.toAlgHom 𝒪[F] C κ

variable (hπ : maximalIdeal 𝒪[F] = Ideal.span {π}) (B : Nilp.{u, v} 𝒪[F] π)

/-- Reducing the target of an uncompleted coefficient map factors through the
actual residue field of the unramified integer ring. -/
def unramifiedResidueMap (g : C →ₐ[𝒪[F]] B.obj) : κ →ₐ[𝒪[F]] Reduction π B.obj :=
  Ideal.Quotient.liftₐ (maximalIdeal C) ((reductionQuotient π B.obj).comp g) fun x hx => by
    have hm : x ∈ Ideal.span {algebraMap 𝒪[F] C π} :=
      (fixedFieldMaximalIdeal_eq_span F π hπ) ▸ hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hm
    change reductionQuotient π B.obj (g (algebraMap 𝒪[F] C π * y)) = 0
    rw [map_mul, g.commutes, map_mul, reductionQuotient_uniformizer, zero_mul]

@[simp]
theorem unramifiedResidueMap_comp (g : C →ₐ[𝒪[F]] B.obj) :
    (B.unramifiedResidueMap hπ g).comp σ₀ = (reductionQuotient π B.obj).comp g :=
  Ideal.Quotient.liftₐ_comp _ _ _

/-- Formal étaleness identifies maps from uncompleted coefficients with their
actual residue coordinates. -/
def unramifiedResidueMapEquiv : (C →ₐ[𝒪[F]] B.obj) ≃ (κ →ₐ[𝒪[F]] Reduction π B.obj) where
  toFun := B.unramifiedResidueMap hπ
  invFun g := B.liftEtale (g.comp σ₀)
  left_inv g := by
    symm
    apply B.liftEtale_unique
    exact (B.unramifiedResidueMap_comp hπ g).symm
  right_inv g := by
    have he : (B.unramifiedResidueMap hπ (B.liftEtale (g.comp σ₀))).comp σ₀ = g.comp σ₀ := by
      rw [unramifiedResidueMap_comp, reductionQuotient_comp_liftEtale]
    apply AlgHom.ext
    intro x
    obtain ⟨y, rfl⟩ := residue_surjective x
    exact AlgHom.congr_fun he y

/-- Actual maps from the completed unramified coefficients correspond to
actual residue maps on every affine nilpotent test. -/
def completedUnramifiedResidueMapEquiv : (Ĉ →ₐ[𝒪[F]] B.obj) ≃ (κ →ₐ[𝒪[F]] Reduction π B.obj) :=
  (B.completedUnramifiedMapEquiv hπ).trans (B.unramifiedResidueMapEquiv hπ)

/-- The completed-coefficient bijection gives the same residue map as actual
reduction of the original map. -/
theorem completedUnramifiedResidueMapEquiv_comp (g : Ĉ →ₐ[𝒪[F]] B.obj) :
    (B.completedUnramifiedResidueMapEquiv hπ g).comp (completedUnramifiedReduction F) =
      (reductionQuotient π B.obj).comp g := by
  let B₀ := (reductionFunctor 𝒪[F] π).obj B
  apply (B₀.completedUnramifiedMapEquiv hπ).injective
  apply AlgHom.ext
  intro x
  change (B.completedUnramifiedResidueMapEquiv hπ g)
    (completedUnramifiedReduction F (toCompletedUnramifiedIntegers F x)) =
      reductionQuotient π B.obj (g (toCompletedUnramifiedIntegers F x))
  change (B.completedUnramifiedResidueMapEquiv hπ g)
    (completedUnramifiedResidueEquiv F (residue _ (toCompletedUnramifiedIntegers F x))) = _
  rw [completedUnramifiedResidueEquiv_residue]
  exact AlgHom.congr_fun (B.unramifiedResidueMap_comp hπ
    (g.comp (toCompletedUnramifiedIntegers F))) x

/-- The equivalence commutes with base change of actual Nilp test algebras. -/
theorem completedUnramifiedResidueMapEquiv_natural {B' : Nilp.{u, v} 𝒪[F] π}
    (f : B ⟶ B') (g : Ĉ →ₐ[𝒪[F]] B.obj) :
    B'.completedUnramifiedResidueMapEquiv hπ (f.hom.hom.comp g) =
      (reductionMap f.hom.hom).comp (B.completedUnramifiedResidueMapEquiv hπ g) := by
  apply AlgHom.ext
  intro x
  obtain ⟨y, rfl⟩ := residue_surjective x
  let g₀ := g.comp (toCompletedUnramifiedIntegers F)
  have h₁ := AlgHom.congr_fun (B'.unramifiedResidueMap_comp hπ (f.hom.hom.comp g₀)) y
  have h₂ := AlgHom.congr_fun (B.unramifiedResidueMap_comp hπ g₀) y
  change (B'.unramifiedResidueMap hπ (f.hom.hom.comp g₀)) (residue _ y) =
    reductionMap f.hom.hom ((B.unramifiedResidueMap hπ g₀) (residue _ y))
  exact h₁.trans ((reductionMap_quotient f.hom.hom (g₀ y)).symm.trans
    (congrArg (reductionMap f.hom.hom) h₂.symm))

end Langlands.FormalGroup.Nilp
